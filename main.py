"""SCC0640 - Prototipo do Sistema de Gestao de Eventos e Espacos (Grupo Ratos de SQL).

v2: executa as 10 consultas do Projeto.txt e resolve questoes de prova/treinamento
(SELECT, janela/CTE, DDL, trigger PL/pgSQL e correcao de consulta) com um modelo
local no Ollama, de forma concisa e validada no PostgreSQL.
"""
import getpass
import json
import re
import sys
import time
import unicodedata
from contextlib import contextmanager
from pathlib import Path

import psycopg
from ollama import Client

BASE_DIR = Path(__file__).resolve().parent
config = {}  # preenchido em main()

LIMITE_LINHAS = 200   # linhas exibidas por resultado
LARGURA_MAX = 45      # largura maxima de uma coluna na tela

ESCRITA = {"ddl", "trigger"}                      # tipos que alteram o esquema
TIPOS = {"sql", "analitica", "ddl", "trigger", "debug"}
NUM_PREDICT = {"sql": 700, "analitica": 800, "ddl": 900, "trigger": 1100, "debug": 800}

SISTEMA = (
    "Você é especialista em PostgreSQL 16. Responda SOMENTE no formato pedido: sem explicações, "
    "sem comentários SQL, sem texto extra. Use estritamente as tabelas e colunas do esquema. "
    "Valores de status/tipo ficam em MAIÚSCULAS conforme os CHECK (ex.: 'CONFIRMADA', 'ESPERA'). "
    "Escreva SQL compacto, com identificadores em minúsculas."
)

_SQL_BASE = (
    "Um único bloco ```sql com UMA consulta (SELECT ou WITH ... SELECT). Use exatamente os nomes/aliases "
    "de colunas pedidos, na ordem pedida, e o ORDER BY pedido. Respeite restrições do enunciado "
    "('somente as tabelas X', 'sem funções de janela'). Dicas: 'não possui nenhuma' -> NOT EXISTS; "
    "contagem de itens distintos -> COUNT(DISTINCT ...) com GROUP BY/HAVING."
)
INSTRUCOES = {
    "sql": _SQL_BASE,
    "analitica": _SQL_BASE + (
        " Janelas: PARTITION BY/ORDER BY com o desempate pedido; acumulado -> SUM(...) OVER (PARTITION BY ... "
        "ORDER BY ... ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) (use ROWS, não RANGE); posição -> "
        "ROW_NUMBER(); contagem incluindo zeros -> LEFT JOIN com o filtro de status no ON (ou subconsulta); "
        "agregue em CTE antes de aplicar a janela."
    ),
    "ddl": (
        "Um único bloco ```sql apenas com o DDL necessário (CREATE TABLE / ALTER TABLE / CREATE UNIQUE INDEX), "
        "na ordem de execução, cada comando terminado em ';'. Garanta as regras por PK, FK (ON DELETE RESTRICT "
        "quando a exclusão for proibida), UNIQUE, NOT NULL, CHECK e, para unicidade condicional, índice único "
        "parcial (CREATE UNIQUE INDEX ... WHERE ...). Não use triggers se proibido. Dê nome às constraints e use "
        "tipos iguais aos das colunas referenciadas."
    ),
    "trigger": (
        "Um único bloco ```sql com: (1) CREATE OR REPLACE FUNCTION ... RETURNS trigger LANGUAGE plpgsql AS $$ ... $$; "
        "(2) CREATE TRIGGER ... BEFORE ... FOR EACH ROW EXECUTE FUNCTION ...; Rejeite com RAISE EXCEPTION e retorne NEW. "
        "OLD só existe em UPDATE: use-o apenas sob IF TG_OP = 'UPDATE' (em INSERT causa erro). Conte com "
        "SELECT COUNT(*) ... excluindo o vínculo antigo quando for UPDATE. Sem comentários."
    ),
    "debug": (
        "Formato EXATO:\nDIAGNÓSTICO: <no máximo 60 palavras, direto ao ponto>\n```sql\n<consulta corrigida>\n```\n"
        "Dicas: filtro no WHERE sobre a tabela do lado opcional de um LEFT JOIN o transforma em INNER JOIN "
        "(mova para o ON); verifique também GROUP BY, COUNT(*) vs COUNT(coluna), DISTINCT e produto cartesiano."
    ),
}


# --------------------------------------------------------------------------- projeto / esquema
def carregar_consultas(texto):
    """Extrai (objetivo, sql) de cada CONSULTA da secao 4 do Projeto.txt."""
    secao = texto.split("4. CONSULTAS", 1)[1].split("FIM DO ARQUIVO", 1)[0]
    consultas = []
    for bloco in re.split(r"^CONSULTA \d+\s*$", secao, flags=re.M)[1:]:
        objetivo = re.search(r"^OBJETIVO:\s*(.+)$", bloco, flags=re.M).group(1).strip()
        sql = bloco.split("SQL:", 1)[1]
        sql = "\n".join(l for l in sql.splitlines() if not l.startswith("=")).strip()
        consultas.append((objetivo, sql))
    return consultas


def _norm(s):
    """Minusculas e sem acentos (para casar palavras do enunciado com nomes de tabelas)."""
    return unicodedata.normalize("NFD", s).encode("ascii", "ignore").decode().lower()


def _compactar(t):
    t = re.sub(r"[ \t]*--[^\n]*", "", t)
    t = re.sub(r"[ \t]+", " ", t)
    return re.sub(r"\n\s*\n+", "\n", t).strip()


def carregar_esquema(texto_ddl):
    """Indexa o DDL: texto compacto por tabela, FKs (pais) e colunas -> tabelas."""
    tabelas = {}
    for m in re.finditer(r"CREATE TABLE\s+(?:IF NOT EXISTS\s+)?(?:\w+\.)?(\w+).*?\n\);", texto_ddl, flags=re.S | re.I):
        tabelas[m.group(1).lower()] = m.group(0)
    for m in re.finditer(r"ALTER TABLE\s+(?:ONLY\s+)?(?:\w+\.)?(\w+)\s.*?;", texto_ddl, flags=re.S | re.I):
        if m.group(1).lower() in tabelas:
            tabelas[m.group(1).lower()] += "\n" + m.group(0)
    tabelas = {n: _compactar(t) for n, t in tabelas.items()}
    refs, colunas = {}, {}
    ignorar = {"constraint", "primary", "foreign", "unique", "check", "create", "exclude", "alter"}
    for nome, t in tabelas.items():
        refs[nome] = {r.lower() for r in re.findall(r"REFERENCES\s+(?:\w+\.)?(\w+)", t, flags=re.I)} - {nome}
        for linha in t.splitlines()[1:]:
            m = re.match(r"\s*(\w+)\s+\w", linha)
            if m and m.group(1).lower() not in ignorar:
                colunas.setdefault(m.group(1).lower(), set()).add(nome)
    return {"tabelas": tabelas, "refs": refs, "colunas": colunas}


def esquema_para(esq, enunciado, completo=False):
    """Devolve (texto_do_esquema, nomes) so com as tabelas relevantes (+ tabelas referenciadas por FK)."""
    tabelas = esq["tabelas"]
    if not completo:
        q = _norm(enunciado)
        achadas = set()
        for nome in tabelas:
            partes = nome.split("_")
            radicais = [p[:max(4, len(p) - 3)] for p in partes]
            if re.search(rf"\b{re.escape(nome)}\b", q):
                achadas.add(nome)
            elif len(partes) == 1 and re.search(rf"\b{re.escape(radicais[0])}\w*", q):
                achadas.add(nome)
            elif len(partes) > 1 and all(re.search(rf"\b{re.escape(r)}\w*", q) for r in radicais):
                achadas.add(nome)
        for tok in set(re.findall(r"\b[a-z]+(?:_[a-z0-9]+)+\b", q)):   # colunas citadas (ex.: exige_inscricao)
            donos = esq["colunas"].get(tok, set())
            if 0 < len(donos) <= 2:
                achadas |= donos
        final = set(achadas)
        for t in achadas:
            final |= esq["refs"].get(t, set())
        if final and len(final) < 0.7 * len(tabelas):
            nomes = [n for n in tabelas if n in final]
            return "\n\n".join(tabelas[n] for n in nomes), nomes
    nomes = list(tabelas)
    return "\n\n".join(tabelas.values()), nomes


# --------------------------------------------------------------------------- tipo e divisao de questoes
def detectar_tipo(enunciado):
    t = _norm(enunciado)
    t = re.sub(r"sem\s+(?:utilizar|usar|uso de)?\s*triggers?", " ", t)   # "sem utilizar triggers" nao e trigger
    if re.search(r"\bselect\b", t) and re.search(
            r"diagnostic|falha|corrig|corrij|consulta abaixo|query abaixo|problema central|errad|incorret|\bbug\b", t):
        return "debug"
    if re.search(r"\btriggers?\b|gatilho|plpgsql|pl/pgsql", t):
        return "trigger"
    if re.search(r"\bddl\b|alter table|create table|create index|nova tabela|tabela propria|evolucao do esquema", t):
        return "ddl"
    if re.search(r"window|\bover\s*\(|acumulad|posicao cronologica|row_number|\brank|partition|particionamento"
                 r"|\bcte\b|\blag\b|\blead\b|media movel", t):
        return "analitica"
    return "sql"


def extrair_flags(texto):
    """Prefixos opcionais: /ddl /trigger /sql /analitica /debug /pensar /rapido /full."""
    m = re.match(r"\s*((?:/[a-z]+\s*)+)", texto, flags=re.I)
    if not m:
        return set(), texto
    return {f.lower() for f in re.findall(r"/([a-z]+)", m.group(1))}, texto[m.end():]


def dividir_questoes(texto):
    """Separa 'QUESTÃO n' e remove rodape/template do PDF. Sem marcadores = uma unica questao."""
    texto = re.split(r"Template do arquivo", texto, maxsplit=1, flags=re.I)[0]
    texto = re.sub(r"SCC0640\s*-\s*Treinamento.*?Page\s+\d+\s+of\s+\d+", " ", texto, flags=re.S | re.I)
    marcas = list(re.finditer(r"^\s*QUEST[ÃA]O\s+(\d+)\b", texto, flags=re.M | re.I))
    if not marcas:
        return [("", texto.strip())]
    blocos = []
    for i, m in enumerate(marcas):
        fim = marcas[i + 1].start() if i + 1 < len(marcas) else len(texto)
        blocos.append((f"Q{m.group(1)}", texto[m.start():fim].strip()))
    return blocos


def ler_arquivo(caminho):
    p = Path(caminho.strip().strip("\"'")).expanduser()
    if not p.exists() and not p.is_absolute():
        p = BASE_DIR / p
    if not p.exists():
        print(f"Arquivo não encontrado: {caminho}")
        return None
    if p.suffix.lower() == ".pdf":
        try:
            from pypdf import PdfReader
        except ImportError:
            print("Para ler PDF instale: pip install pypdf")
            return None
        return "\n".join((pg.extract_text() or "") for pg in PdfReader(str(p)).pages)
    return p.read_text(encoding="utf-8", errors="replace")


def ler_enunciado():
    print("Cole a(s) questão(ões) e termine com 2 linhas em branco (ou Ctrl+D / Ctrl+Z+Enter).")
    print("Atalhos: @arquivo.pdf|.txt | prefixos /ddl /trigger /sql /analitica /debug /pensar /rapido /full")
    linhas = []
    while True:
        try:
            linha = input()
        except EOFError:
            break
        if not linha and linhas and not linhas[-1]:
            break
        linhas.append(linha)
    return "\n".join(linhas).strip()


# --------------------------------------------------------------------------- modelo
def _consumir(fluxo):
    partes, n, t0 = [], 0, time.time()
    for chunk in fluxo:
        msg = chunk["message"]
        c = msg.get("content") or ""
        th = msg.get("thinking") or ""
        if c or th:
            n += 1
        partes.append(c)
        if n and n % 5 == 0:
            fase = "pensando" if (th and not c) else "escrevendo"
            print(f"\r  {fase}... {n} tokens ({n / max(time.time() - t0, 1e-6):.1f} tok/s)   ", end="", flush=True)
    print("\r" + " " * 60 + "\r", end="")
    return "".join(partes), n


def chamar_modelo(client, mensagens, tipo, pensar):
    cfg = config["ollama"]
    limite = cfg.get("num_predict", NUM_PREDICT[tipo])
    if pensar:
        limite += cfg.get("think_budget", 3000)
    opcoes = {
        "temperature": cfg.get("temperature", 0.1),
        "top_p": 0.9,
        "num_ctx": cfg.get("num_ctx", 6144),
        "num_predict": limite,
    }
    if cfg.get("num_thread"):
        opcoes["num_thread"] = cfg["num_thread"]
    kw = dict(model=cfg["model"], messages=mensagens, options=opcoes, stream=True,
              keep_alive=cfg.get("keep_alive", "30m"))
    kw["think"] = pensar
    try:
        return _consumir(client.chat(**kw))
    except TypeError:                      # biblioteca ollama antiga, sem 'think'
        kw.pop("think")
        return _consumir(client.chat(**kw))
    except Exception as e:
        if "think" in str(e).lower() and "think" in kw:   # modelo sem suporte a 'think'
            kw.pop("think")
            return _consumir(client.chat(**kw))
        raise


def pre_aquecer(client):
    """Carrega o modelo na RAM antes da primeira pergunta."""
    cfg = config["ollama"]
    try:
        print(f"Carregando {cfg['model']} na memória...")
        client.generate(model=cfg["model"], prompt="", keep_alive=cfg.get("keep_alive", "30m"))
    except Exception as e:
        print(f"Aviso: não foi possível pré-carregar o modelo ({e}).")


def sem_think(texto):
    return re.sub(r"<think>.*?(?:</think>|\Z)", "", texto, flags=re.S | re.I).strip()


def limpar_sql(sql):
    linhas = [l.rstrip() for l in sql.splitlines() if not l.lstrip().startswith("--")]
    return re.sub(r"\n{3,}", "\n\n", "\n".join(linhas)).strip()


def extrair(resposta, tipo):
    """Devolve (sql, diagnostico). Aceita cercas ```, cerca nao fechada e texto cru."""
    texto = sem_think(resposta)
    blocos = re.findall(r"```[a-zA-Z]*[ \t]*\n(.*?)```", texto, flags=re.S)
    if not blocos:
        aberto = re.search(r"```[a-zA-Z]*[ \t]*\n(.*)\Z", texto, flags=re.S)
        if aberto:
            blocos = [aberto.group(1)]
    if not blocos:
        ini = re.search(r"\b(WITH|SELECT|CREATE|ALTER)\b", texto, flags=re.I)
        blocos = [texto[ini.start():]] if ini else []
    diag = None
    if tipo == "debug":
        m = re.search(r"DIAGN[ÓO]STICO\s*:?\s*(.*?)(?=\n\s*(?:CORRE[ÇC][ÃA]O|```)|\Z)", texto, flags=re.S | re.I)
        diag = " ".join(m.group(1).split()) if m else None
    if not blocos:
        return None, diag
    if tipo in ESCRITA:
        return "\n\n".join(limpar_sql(b) for b in blocos), diag
    sql = limpar_sql(blocos[-1] if tipo == "debug" else blocos[0])
    return sql.split(";")[0].strip(), diag


def montar_mensagens(esquema_txt, enunciado, tipo):
    usuario = (f"ESQUEMA:\n{esquema_txt}\n\nFORMATO ({tipo}):\n{INSTRUCOES[tipo]}\n\n"
               f"QUESTÃO:\n{enunciado}")
    return [{"role": "system", "content": SISTEMA}, {"role": "user", "content": usuario}]


# --------------------------------------------------------------------------- banco
def formatar(valor):
    if valor is None:
        return ""
    texto = str(valor).replace("\n", " ")
    return texto if len(texto) <= LARGURA_MAX else texto[:LARGURA_MAX - 3] + "..."


def imprimir_tabela(colunas, linhas):
    if not linhas:
        print("(nenhuma linha retornada)")
        return
    celulas = [[formatar(v) for v in linha] for linha in linhas[:LIMITE_LINHAS]]
    larguras = [max(len(c), *(len(l[i]) for l in celulas)) for i, c in enumerate(colunas)]
    print(" | ".join(c.ljust(w) for c, w in zip(colunas, larguras)))
    print("-+-".join("-" * w for w in larguras))
    for linha in celulas:
        print(" | ".join(v.ljust(w) for v, w in zip(linha, larguras)))
    extra = len(linhas) - LIMITE_LINHAS
    print(f"({len(linhas)} linha(s)" + (f"; {extra} não exibida(s))" if extra > 0 else ")"))


@contextmanager
def modo(conn, somente_leitura):
    """Transacao que SEMPRE termina em rollback; somente leitura salvo para testar DDL."""
    conn.rollback()
    conn.read_only = somente_leitura
    try:
        yield
    finally:
        conn.rollback()
        conn.read_only = True


def executar(conn, sql):
    """Executa em transacao somente leitura e sempre desfaz ao final."""
    try:
        with modo(conn, True), conn.cursor() as cur:
            cur.execute(sql)
            if cur.description is None:
                print("(comando executado sem retorno de linhas)")
                return
            colunas = [d.name for d in cur.description]
            linhas = cur.fetchall()
        imprimir_tabela(colunas, linhas)
    except psycopg.Error as e:
        print(f"Erro ao executar a consulta: {e}".strip())


def validar(conn, sql, tipo):
    """('ok'|'erro'|'pulado', mensagem). SELECT -> EXPLAIN; DDL/trigger -> teste em transacao revertida."""
    if re.search(r"\bcommit\b", sql, flags=re.I):
        return "erro", "o SQL contém COMMIT"
    if tipo in ESCRITA:
        if not config.get("validar_ddl", True):
            return "pulado", ""
    elif not re.match(r"\s*(?:with|select|\()", sql, flags=re.I):
        return "erro", "a resposta deve ser um SELECT/WITH"
    try:
        with modo(conn, tipo not in ESCRITA), conn.cursor() as cur:
            cur.execute(sql if tipo in ESCRITA else "EXPLAIN " + sql)
        return "ok", ""
    except psycopg.Error as e:
        return "erro", " ".join(str(e).split())[:300]


def ler_parametros(db):
    print("Parâmetros de conexão com o PostgreSQL (Enter mantém o valor do config.json):")
    for chave in ("host", "port", "dbname", "user"):
        valor = input(f"  {chave} [{db[chave]}]: ").strip()
        if chave == "port" and valor and not valor.isdigit():
            print("  porta inválida, mantendo", db[chave])
            continue
        if valor:
            db[chave] = int(valor) if chave == "port" else valor
    ler_senha = getpass.getpass if sys.stdin.isatty() else input
    senha = ler_senha("  password [config.json]: ").strip()
    if senha:
        db["password"] = senha


def conectar():
    db = config["database"]
    while True:
        ler_parametros(db)
        try:
            conn = psycopg.connect(host=db["host"], port=db["port"], dbname=db["dbname"],
                                   user=db["user"], password=db["password"])
        except psycopg.Error as e:
            print(f"Não foi possível conectar: {e}".strip())
            if input("Tentar novamente? [S/n]: ").strip().lower() == "n":
                raise SystemExit(1)
            continue
        conn.execute("SET statement_timeout = '30s'")
        conn.commit()
        conn.read_only = True
        print(f"Conectado a {db['dbname']} em {db['host']}:{db['port']}.")
        return conn


# --------------------------------------------------------------------------- resolucao
def responder(conn, client, esq, rotulo, enunciado, tipo, flags):
    t0 = time.time()
    cfg = config["ollama"]
    pensar = False if "rapido" in flags else ("pensar" in flags or bool(cfg.get("think", False)))
    esquema_txt, nomes = esquema_para(esq, enunciado, completo="full" in flags)
    mensagens = montar_mensagens(esquema_txt, enunciado, tipo)
    print(f"\n[{rotulo or 'Questão'}] tipo: {tipo} | pensar: {'sim' if pensar else 'não'} | tabelas: {', '.join(nomes)}")

    sql = diag = None
    status, msg, tokens = "erro", "", 0
    tentativas = max(1, int(cfg.get("max_tentativas", 2)))
    for i in range(1, tentativas + 1):
        try:
            resposta, n = chamar_modelo(client, mensagens, tipo, pensar)
        except KeyboardInterrupt:
            print("\nCancelado.")
            return None
        except Exception as e:
            print(f"Erro ao consultar o Ollama: {e}")
            print("Verifique se o Ollama está em execução e se o modelo foi baixado.")
            return None
        tokens += n
        sql, diag = extrair(resposta, tipo)
        if sql:
            status, msg = validar(conn, sql, tipo)
        else:
            status, msg = "erro", "resposta sem bloco de código SQL"
        if status != "erro":
            break
        if i < tentativas:
            print(f"  ↻ corrigindo (erro: {msg[:110]})")
            mensagens += [
                {"role": "assistant", "content": sem_think(resposta)},
                {"role": "user", "content": f"O PostgreSQL retornou: {msg}\nCorrija e responda de novo "
                                            "SOMENTE no mesmo formato."},
            ]

    if not sql:
        print("O modelo não retornou SQL utilizável. Resposta bruta:")
        print(sem_think(resposta))
        return None

    linha = "-" * 60
    print(linha)
    if tipo == "debug":
        palavras = len(diag.split()) if diag else 0
        aviso = " [acima de 60!]" if palavras > 60 else ""
        print(f"DIAGNÓSTICO ({palavras} palavras){aviso}: {diag or '(não informado)'}")
        print("CORREÇÃO:")
    saida = sql if (tipo in ESCRITA or sql.endswith(";")) else sql + ";"
    print(saida)
    print(linha)
    selo = {"ok": "✓ validado no PostgreSQL", "pulado": "validação desativada"}.get(status, f"⚠ NÃO validado: {msg}")
    print(f"{time.time() - t0:.1f}s | {tokens} tokens | {selo}")

    if tipo not in ESCRITA and status != "erro":
        if input("Executar no banco? [s/N]: ").strip().lower() == "s":
            executar(conn, sql)
    return saida


def resolver(conn, client, esq, bruto):
    flags, texto = extrair_flags(bruto)
    if texto.lstrip().startswith("@"):
        texto = ler_arquivo(texto.lstrip()[1:].splitlines()[0])
        if not texto:
            return
    forcado = next((f for f in flags if f in TIPOS), None)
    for rotulo, enunciado in dividir_questoes(texto):
        if enunciado:
            responder(conn, client, esq, rotulo, enunciado, forcado or detectar_tipo(enunciado), flags)


def main():
    with open(BASE_DIR / "config.json", encoding="utf-8") as f:
        config.update(json.load(f))
    projeto_path = BASE_DIR.parent / "Projeto.txt"
    if not projeto_path.exists():
        projeto_path = BASE_DIR.parent.parent / "Projeto.txt"   # zip extraido com pasta duplicada
    if not projeto_path.exists():
        print("Erro: Projeto.txt não encontrado.")
        raise SystemExit(1)
    projeto = projeto_path.read_text(encoding="utf-8")
    try:
        ddl = projeto.split("3. DDL COMPLETO", 1)[1].split("4. CONSULTAS", 1)[0].strip()
    except IndexError:
        print("Erro: seção '3. DDL COMPLETO' não encontrada em Projeto.txt.")
        raise SystemExit(1)

    consultas = carregar_consultas(projeto)
    esq = carregar_esquema(ddl)
    cfg = config["ollama"]
    client = Client(host=cfg["host"], timeout=cfg.get("timeout", 900))
    print("=" * 60)
    print("SCC0640 - Sistema de Gestão de Eventos e Espaços (Ratos de SQL)")
    print("=" * 60)
    conn = conectar()
    pre_aquecer(client)
    opcao_q = len(consultas) + 1
    try:
        while True:
            print()
            for i, (objetivo, _) in enumerate(consultas, 1):
                print(f"{i:>3}. {objetivo}")
            print(f"{opcao_q:>3}. Resolver pergunta/questão de prova (SQL, janela/CTE, DDL, trigger, correção)")
            print(f"{0:>3}. Sair")
            opcao = input("Opção: ").strip()
            print()
            if opcao == "0":
                break
            if opcao == str(opcao_q):
                texto = ler_enunciado()
                if texto:
                    resolver(conn, client, esq, texto)
            elif opcao.isdigit() and 1 <= int(opcao) <= len(consultas):
                objetivo, sql = consultas[int(opcao) - 1]
                print(f"CONSULTA {opcao}: {objetivo}")
                executar(conn, sql)
            else:
                print("Opção inválida.")
            input("\nEnter para voltar ao menu...")
    except (EOFError, KeyboardInterrupt):
        print()
    finally:
        conn.close()
    print("Até logo.")


if __name__ == "__main__":
    try:
        main()
    except (EOFError, KeyboardInterrupt):
        print("\nEncerrado.")