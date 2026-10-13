#!/usr/bin/env python3
"""
Linha de FECHAMENTO ATK — CLOSED_MATH calculado pelo kernel, no mesmo formato das linhas
condicional e de explosão.

Formato (por problema):
  1. alvo exato      — `targets`: claim → tipo Lean (o enunciado oficial e a sua negação);
  2. certificado      — `closures`: declaração SEM hipóteses cujo tipo é EXATAMENTE um alvo;
  3. portão           — o kernel compila `theorem _ : <alvo> := @decl` e os axiomas têm de estar em
                        {propext, Classical.choice, Quot.sound};
  4. bandeira         — CLOSED_MATH[problema] = true  ⇔  algum certificado foi aceito;
                        OPEN_MATH[problema] = ¬ CLOSED_MATH[problema].  Nunca escrita à mão.

Rotas registradas (não fecham sozinhas; mostram por onde um certificado pode chegar):
  ponte    — `bridges`:    `H → alvo`      (fecha quando H tiver certificado);
  explosão — `explosions`: `W → ¬ alvo` ou `W → alvo` (fecha quando houver testemunha W).

Controles (sempre; se algum falhar, o portão é INVÁLIDO e o script sai com 1):
  + decisão verdadeira de um problema-brinquedo é aceita;
  − alvo introduzido por `axiom` é recusado;      − `sorry` é recusado;
  − `alvo ∨ ¬ alvo` (terceiro excluído) compila, mas NÃO é alvo admissível;
  − a ponte oferecida como certificado é recusada (tipo errado: falta H);
  − a linha de explosão oferecida como certificado é recusada (falta a testemunha).
"""
import argparse
import json
import os
import re
import subprocess
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def make_runner(root, gen, rep, imports):
    header = "".join(f"import {m}\n" for m in imports)

    def run_check(name, decl_type, term, prelude=""):
        os.makedirs(gen, exist_ok=True)
        thm = f"atkGate_{name}"
        path = os.path.join(gen, f"Check_{name}.lean")
        src = f"{header}\n{prelude}\ntheorem {thm} : {decl_type} := {term}\n\n#print axioms {thm}\n"
        open(path, "w", encoding="utf-8").write(src)
        try:
            proc = subprocess.run(["lake", "env", "lean", path], cwd=root, capture_output=True,
                                  text=True, timeout=1800)
            out, code = proc.stdout + proc.stderr, proc.returncode
        except Exception as exc:  # noqa: BLE001
            out, code = f"falha ao executar lean: {exc}", 99
        errors = [l for l in out.splitlines() if ": error" in l or l.startswith("error")]
        axioms = None
        m = re.search(rf"'{thm}' depends on axioms: \[([^\]]*)\]", out, re.S)
        if m:
            axioms = [a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()]
        elif re.search(rf"'{thm}' does not depend on any axioms", out):
            axioms = []
        kernel_ok = code == 0 and not errors and axioms is not None
        extra = sorted(set(axioms or []) - ALLOWED)
        accepted = kernel_ok and not extra
        if not kernel_ok:
            why = "kernel recusou (tipo/elaboração)" if errors else f"lean saiu com {code}"
        elif extra:
            why = "axiomas proibidos: " + ", ".join(extra)
        else:
            why = "aceito: tipo exato, axiomas padrão"
        open(os.path.join(rep, f"closure_{name}.log"), "w", encoding="utf-8").write(src + "\n----\n" + out)
        return {"name": name, "type": decl_type, "term": term, "kernel_ok": kernel_ok,
                "axioms": axioms, "accepted": accepted, "reason": why, "errors": errors[:4]}

    return run_check


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--registry", default=None)
    ap.add_argument("--reports", default=None)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    reg_path = a.registry or os.path.join(root, "closure", "registry.json")
    rep = a.reports or os.path.join(root, "reports")
    os.makedirs(rep, exist_ok=True)
    reg = json.load(open(reg_path, encoding="utf-8"))
    run = make_runner(root, os.path.join(root, "closure", "_gen"), rep, reg.get("imports", ["ATK"]))
    problem = reg["problem"]
    targets = reg["targets"]

    # ---------- controles ----------
    toy = ("¬ ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 1 < x → 1 < y → 1 < z → "
           "A ^ x + B ^ y = C ^ z → 1 < Nat.gcd A (Nat.gcd B C)")
    main_claim = reg["main_claim"]
    T = targets[main_claim]
    controls = [
        ("pos_toy", toy, "ATK.Exact.beal_needs_exponents_gt_two", "", True,
         "decisão verdadeira de problema-brinquedo (Beal com expoente 2 é falso)"),
        ("neg_axiom", T, "atkFakeTarget", f"axiom atkFakeTarget : {T}\n", False,
         "alvo introduzido como axioma"),
        ("neg_sorry", T, "sorry", "", False, "sorry"),
    ]
    for b in reg.get("bridges", []):
        controls.append((f"neg_bridge_{len(controls)}", targets[b["claim"]], f"@{b['decl']}", "",
                         False, f"ponte {b['decl']} oferecida como certificado (falta H)"))
    for x in reg.get("explosions", []):
        controls.append((f"neg_expl_{len(controls)}", targets[x["claim"]], f"@{x['decl']}", "",
                         False, f"linha de explosão {x['decl']} oferecida como certificado (falta W)"))
    rows, valid = [], True
    for name, typ, term, prelude, expect, label in controls:
        r = run(name, typ, term, prelude)
        r.update(label=label, expected=expect, ok=(r["accepted"] == expect))
        valid &= r["ok"]
        rows.append(r)
    # terceiro excluído: o kernel aceita, o portão recusa (não é alvo admissível)
    r = run("em_vacuous", f"({T}) ∨ ¬ ({T})", "Classical.em _")
    r.update(label=f"terceiro excluído para {main_claim} — teorema, NÃO é alvo", expected=False,
             kernel_says_theorem=r["accepted"])
    r["ok"] = r["kernel_says_theorem"]
    r["accepted"] = False
    r["reason"] = ("o kernel prova `alvo ∨ ¬alvo`; o portão recusa: não decide nada"
                   if r["ok"] else r["reason"])
    valid &= r["ok"]
    rows.append(r)

    # ---------- rotas ----------
    route_rows = []
    for kind in ("bridges", "explosions"):
        for i, x in enumerate(reg.get(kind, [])):
            typ = f"{x['hypothesis']} → {targets[x['claim']]}"
            r = run(f"{kind}_{i}", typ, f"@{x['decl']}")
            route_rows.append({"kind": "ponte" if kind == "bridges" else "explosão", **x,
                               "type": typ, "accepted": r["accepted"], "reason": r["reason"],
                               "axioms": r["axioms"], "status_of_hypothesis": x.get("status", "")})

    # ---------- certificados ----------
    cert_rows = []
    for i, c in enumerate(reg.get("closures", [])):
        row = dict(c)
        if c["claim"] not in targets:
            row.update(accepted=False, reason="alvo não admissível")
        elif not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'₀-₉]*", c["decl"]):
            row.update(accepted=False, reason="nome inválido")
        else:
            r = run(f"closure_{i}", targets[c["claim"]], f"@{c['decl']}")
            row.update(accepted=r["accepted"], reason=r["reason"], axioms=r["axioms"])
        cert_rows.append(row)

    # ---------- regime suave: sub-alvos (versões relaxadas que já são teoremas) ----------
    sub_rows = []
    for i, st in enumerate(reg.get("subtargets", [])):
        r = run(f"sub_{i}", st["type"], st.get("term") or f"@{st['decl']}")
        sub_rows.append({**st, "accepted": r["accepted"], "reason": r["reason"], "axioms": r["axioms"]})

    # ---------- bandeiras por alegação ----------
    claims = {}
    for claim in targets:
        acc = [c for c in cert_rows if c["claim"] == claim and c["accepted"]]
        claims[claim] = {
            "CLOSED_MATH": bool(acc),
            "by": [c["decl"] for c in acc],
            "routes": [f"{r['kind']}: {r['decl']} : {r['type']} — "
                       f"{'certificada' if r['accepted'] else 'RECUSADA'}"
                       + (f" · hipótese: {r['status_of_hypothesis']}" if r["status_of_hypothesis"] else "")
                       for r in route_rows if r["claim"] == claim],
        }
    neg = reg.get("negations", {})
    for c1, c2 in neg.items():
        if claims.get(c1, {}).get("CLOSED_MATH") and claims.get(c2, {}).get("CLOSED_MATH"):
            valid = False  # inconsistência: alvo e negação fechados
    closed_any = [c for c, v in claims.items() if v["CLOSED_MATH"]]
    out = {"problem": problem, "gate_valid": valid, "claims": claims,
           "CLOSED_MATH": {c: v["CLOSED_MATH"] for c, v in claims.items()},
           "controls": rows, "routes": route_rows, "closures": cert_rows,
           "CLOSED_MATH_SUB": {st["name"]: st["accepted"] for st in sub_rows}, "subtargets": sub_rows}
    json.dump(out, open(os.path.join(rep, "closure_line.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=2)

    L = [f"## Linha de fechamento — {problem}", "",
         f"Portão {'VÁLIDO' if valid else 'INVÁLIDO'} · alegações fechadas: "
         f"{', '.join(closed_any) if closed_any else 'nenhuma'}", "",
         "| Alegação | Alvo exato | CLOSED_MATH | Certificado | Rotas |", "|---|---|---|---|---|"]
    for c, v in claims.items():
        L.append(f"| {c} | `{targets[c]}` | **{'true' if v['CLOSED_MATH'] else 'false'}** | "
                 f"{', '.join('`'+d+'`' for d in v['by']) or '—'} | {'<br>'.join(v['routes']) or '—'} |")
    if sub_rows:
        L += ["", "### Regime suave — sub-alvos (versões relaxadas; NÃO são o alvo oficial)", "",
              "| Sub-alvo | CLOSED_MATH_SUB | Declaração | Relação com o alvo |", "|---|---|---|---|"]
        for st in sub_rows:
            L.append(f"| {st['name']} | **{'true' if st['accepted'] else 'false'}** | "
                     f"`{st.get('term') or st['decl']}` | {st.get('relation', '')} |")
    L += ["", "### Controles", "", "| Controle | Esperado | Obtido | OK |", "|---|---|---|---|"]
    for r in rows:
        L.append(f"| {r['label']} | {'aceitar' if r['expected'] else 'recusar'} | "
                 f"{'aceito' if r['accepted'] else 'recusado'} ({r['reason']}) | {'✅' if r['ok'] else '❌'} |")
    md = "\n".join(L) + "\n"
    open(os.path.join(rep, "closure_line.md"), "w", encoding="utf-8").write(md)
    print(md)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8").write(md)
    if os.environ.get("GITHUB_ACTIONS"):
        def esc(s):
            return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        flags = " · ".join(f"{c}={'true' if v['CLOSED_MATH'] else 'false'}" for c, v in claims.items())
        print(f"::notice title=CLOSED_MATH[{problem}] {flags} · portão {'VÁLIDO' if valid else 'INVÁLIDO'}::"
              + esc("\n".join(f"{c}: " + (", ".join(v['by']) or "sem certificado") for c, v in claims.items())))
        if sub_rows:
            print(f"::notice title=Regime suave {problem}: {sum(st['accepted'] for st in sub_rows)}/{len(sub_rows)} sub-alvos fechados::" + esc("\n".join(
                f"{'true' if st['accepted'] else 'false'} | {st['name']} | {st['reason']}" for st in sub_rows)))
        print("::notice title=Rotas registradas::" + esc("\n".join(
            f"{r['kind']} {r['decl']} — {'certificada' if r['accepted'] else 'RECUSADA'} ({r['reason']})"
            for r in route_rows) or "nenhuma"))
        print("::notice title=Controles do portão::" + esc("\n".join(
            f"{'OK' if r['ok'] else 'FALHOU'} | {r['label']} | {'aceito' if r['accepted'] else 'recusado'} | {r['reason']}"
            for r in rows)))
    valid = valid and all(st['accepted'] for st in sub_rows)
    return 0 if valid else 1


if __name__ == "__main__":
    sys.exit(main())
