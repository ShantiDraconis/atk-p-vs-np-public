#!/usr/bin/env python3
"""
Auditoria ATK: transforma a saída do kernel Lean em uma tabela de certificação.

Entradas (em reports/):
  file_status.txt   linhas "ATK/X.lean OK" ou "ATK/X.lean FAIL"
  audit_<X>.log     saída de `lake env lean ATK/X.lean` (inclui #print axioms)
  build.log         saída de `lake build`
Saídas:
  reports/report.md, reports/report.json
Código de saída 0 só se TODOS os teoremas esperados estiverem CERTIFIED.

CERTIFIED  = arquivo compilou sem erro E #print axioms ⊆ {propext, Classical.choice, Quot.sound}
NOT_CERTIFIED = qualquer outra coisa (erro, sorryAx, axioma próprio, teorema ausente)
"""
import hashlib, json, os, re, sys, glob

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REP = os.path.join(ROOT, "reports")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

expected = [l.strip() for l in open(os.path.join(ROOT, "scripts", "expected_theorems.txt")) if l.strip()]

status = {}
fs = os.path.join(REP, "file_status.txt")
if os.path.exists(fs):
    for line in open(fs):
        parts = line.split()
        if len(parts) == 2:
            status[parts[0]] = parts[1]

axioms, errors = {}, {}
for log in sorted(glob.glob(os.path.join(REP, "audit_*.log"))):
    text = open(log, encoding="utf-8", errors="replace").read()
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S):
        axioms[m.group(1)] = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        axioms[m.group(1)] = []
    mod = os.path.basename(log)[len("audit_"):-len(".log")]
    errs = [l for l in text.splitlines() if ": error" in l or "error:" in l]
    if errs:
        errors[mod] = errs[:20]

# proibições textuais extras (sorry/admit/axiom declarados)
src_flags = {}
for f in sorted(glob.glob(os.path.join(ROOT, "ATK", "*.lean"))):
    code = re.sub(r"/-.*?-/", "", open(f, encoding="utf-8").read(), flags=re.S)
    code = re.sub(r"--.*", "", code)
    flags = [w for w in ("sorry", "admit") if re.search(rf"\b{w}\b", code)]
    if re.search(r"^\s*axiom\s", code, re.M):
        flags.append("axiom")
    if flags:
        src_flags[os.path.relpath(f, ROOT)] = flags

def module_file(thm):
    return f"ATK/{thm.split('.')[1]}.lean"

rows, certified = [], 0
for thm in expected:
    f = module_file(thm)
    fstat = status.get(f, "NOT_RUN")
    ax = axioms.get(thm)
    if fstat != "OK":
        verdict, why = "NOT_CERTIFIED", f"arquivo {fstat}"
    elif ax is None:
        verdict, why = "NOT_CERTIFIED", "sem saída de #print axioms"
    elif not set(ax) <= ALLOWED:
        verdict, why = "NOT_CERTIFIED", "axiomas extras: " + ", ".join(sorted(set(ax) - ALLOWED))
    elif f in src_flags:
        verdict, why = "NOT_CERTIFIED", "fonte contém " + ", ".join(src_flags[f])
    else:
        verdict, why = "CERTIFIED", ""
        certified += 1
    rows.append({"theorem": thm, "file": f, "file_status": fstat,
                 "axioms": ax, "verdict": verdict, "reason": why})

sha = hashlib.sha256()
for f in sorted(glob.glob(os.path.join(ROOT, "ATK", "*.lean"))) + [os.path.join(ROOT, "ATK.lean")]:
    sha.update(open(f, "rb").read())
src_sha = sha.hexdigest()

def read(p):
    p = os.path.join(ROOT, p)
    return open(p).read().strip() if os.path.exists(p) else "?"

report = {
    "certified": certified, "total": len(expected),
    "lean_toolchain": read("lean-toolchain"),
    "lean_version": read("reports/toolchain.txt"),
    "mathlib_rev": "v4.34.1",
    "sources_sha256": src_sha,
    "commit": os.environ.get("GITHUB_SHA", "local"),
    "theorems": rows, "errors": errors, "source_flags": src_flags,
}
json.dump(report, open(os.path.join(REP, "report.json"), "w"), indent=2, ensure_ascii=False)

state = "CERTIFIED" if certified == len(expected) else "PARTIAL" if certified else "NOT_CERTIFIED"
md = [f"## ATK-KERNEL: {state} — {certified}/{len(expected)} teoremas",
      "",
      f"- Lean: `{report['lean_version']}` · Mathlib `v4.34.1`",
      f"- SHA-256 das fontes: `{src_sha}`",
      f"- Commit: `{report['commit']}`",
      "",
      "| Teorema | Veredito | Axiomas | Motivo |",
      "|---|---|---|---|"]
for r in rows:
    ax = "—" if r["axioms"] is None else (", ".join(r["axioms"]) or "nenhum")
    md.append(f"| `{r['theorem']}` | {'✅' if r['verdict']=='CERTIFIED' else '❌'} {r['verdict']} | {ax} | {r['reason']} |")
if errors:
    md += ["", "### Erros de compilação (primeiras linhas)"]
    for mod, errs in errors.items():
        md.append(f"**{mod}**")
        md.append("```")
        md += errs
        md.append("```")
md += ["", "Escopo: ponte condicional H → alvo. Nenhum destes teoremas prova o alvo sem H; "
       "`OPEN_MATH` continua verdadeiro para RH, P≠NP, NS, YM, BSD, Hodge e Beal."]
open(os.path.join(REP, "report.md"), "w").write("\n".join(md) + "\n")
print("\n".join(md))

# Anotações do Actions (legíveis pela API e na interface): 1 resumo + 1 por módulo (≤ 10 por passo)
if os.environ.get("GITHUB_ACTIONS"):
    def esc(s):
        return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(f"::notice title=ATK-KERNEL {state} {certified}/{len(expected)}::"
          + esc(f"sha256 fontes {src_sha}\nlean {report['lean_version']} · mathlib v4.34.1"))
    by_mod = {}
    for r in rows:
        by_mod.setdefault(r["file"], []).append(r)
    # o Actions guarda no máximo 10 anotações por passo: agrupa os módulos em até 9 avisos
    mods = list(by_mod.items())
    nchunks = min(9, len(mods))
    for i in range(nchunks):
        chunk = mods[i::nchunks]
        names, lines = [], []
        for f, rs in chunk:
            ok = sum(r["verdict"] == "CERTIFIED" for r in rs)
            names.append(f"{f} {ok}/{len(rs)}")
            lines += [f"{r['verdict']} {r['theorem']} [{', '.join(r['axioms']) if r['axioms'] is not None else '—'}]"
                      + (f" ({r['reason']})" if r["reason"] else "") for r in rs]
            mod = os.path.basename(f)[:-len(".lean")]
            for l in errors.get(mod, [])[:6]:
                lines.append("ERRO " + re.sub(r"^.*?ATK/", "ATK/", l)[:300])
        print(f"::notice title={' · '.join(names)}::" + esc("\n".join(lines)))
sys.exit(0 if certified == len(expected) else 1)
