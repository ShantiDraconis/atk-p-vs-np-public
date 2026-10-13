#!/usr/bin/env python3
import json, os, re, hashlib
from pathlib import Path
from datetime import datetime, timezone

ROOT = Path(".")
CFG = ROOT / "final-proof" / "endpoints.json"
OUT = ROOT / "evidence"
OUT.mkdir(exist_ok=True)

cfg = json.loads(CFG.read_text())
endpoints = cfg["endpoints"]
edges = cfg["critical_chain"]
families = cfg.get("families", [])

TEXT_EXTS = {".lean",".md",".json",".yml",".yaml",".txt",".toml"}
SKIP = {".git","evidence",".lake","build","dist","node_modules"}

files = []
for p in ROOT.rglob("*"):
    if not p.is_file() or p.suffix.lower() not in TEXT_EXTS:
        continue
    if any(part in SKIP for part in p.parts):
        continue
    files.append(p)

corpus = {}
for p in files:
    try:
        corpus[str(p)] = p.read_text(errors="ignore")
    except Exception:
        pass

proof_decl = re.compile(r"^\s*(theorem|lemma|def|structure|class|abbrev|instance)\s+([A-Za-z0-9_'.]+)", re.M)
sorry_pat = re.compile(r"\b(sorry|admit|sorryAx)\b")
axiom_pat = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)", re.M)

decls = {}
axioms = []
unsafe_files = []
for path, text in corpus.items():
    for kind,name in proof_decl.findall(text):
        decls.setdefault(name, []).append({"file":path,"kind":kind})
    for name in axiom_pat.findall(text):
        axioms.append({"file":path,"name":name})
    if sorry_pat.search(text):
        unsafe_files.append(path)

def refs_for(name):
    out=[]
    pat=re.compile(r"\b"+re.escape(name)+r"\b")
    for path,text in corpus.items():
        if pat.search(text):
            out.append(path)
    return out

states={}
for ep in endpoints:
    refs=refs_for(ep)
    declared=ep in decls
    unsafe=any(f in unsafe_files for f in refs)
    if declared and not unsafe:
        state="FOUND"
    elif refs:
        state="REFERENCED_ONLY"
    else:
        state="MISSING"
    states[ep]={
        "state":state,
        "declarations":decls.get(ep,[]),
        "references":refs[:50],
        "unsafe_reference":unsafe,
    }

# Fail-closed dependency propagation: an endpoint is only DERIVABLE when every predecessor
# in the configured critical graph is at least FOUND/DERIVABLE.
pred={e:[] for e in endpoints}
for a,b in edges:
    pred.setdefault(b,[]).append(a)

changed=True
while changed:
    changed=False
    for ep in endpoints:
        if states[ep]["state"]!="MISSING":
            continue
        ps=pred.get(ep,[])
        if ps and all(states.get(x,{}).get("state") in {"FOUND","DERIVABLE"} for x in ps):
            states[ep]["state"]="DERIVABLE"
            changed=True

blocked={}
for ep in endpoints:
    if states[ep]["state"] in {"FOUND","DERIVABLE"}:
        continue
    missing=[p for p in pred.get(ep,[]) if states.get(p,{}).get("state") not in {"FOUND","DERIVABLE"}]
    blocked[ep]=missing

# Family index: filenames/tokens beginning with each historical family label.
family_index={}
for fam in families:
    hits=[]
    token=re.compile(r"\b"+re.escape(fam)+r"[A-Za-z0-9_.-]*\b")
    for path,text in corpus.items():
        if token.search(text) or Path(path).name.upper().startswith(fam.upper()):
            hits.append(path)
    family_index[fam]=sorted(set(hits))

now=datetime.now(timezone.utc).isoformat()
report={
    "schema":"final-proof-miner.v1",
    "generated_at":now,
    "files_scanned":len(corpus),
    "families":family_index,
    "axioms_declared":axioms,
    "unsafe_files":sorted(set(unsafe_files)),
    "endpoints":states,
    "blocked_by":blocked,
}

# Terminal status is fail-closed.
terminal=["P01ConstructionGap","G21Pointwise","P02Target","ExternalModelMatch",
          "FinalExternalLiveTwoProducer","FinalExternalCertificate",
          "FINAL_ROOT","FINAL_EXTERNAL_ISSUED","FINAL_PROOF"]
terminal_ok=all(states.get(x,{}).get("state") in {"FOUND","DERIVABLE"} for x in terminal)
report["terminal_status"]="READY_FOR_KERNEL_AUDIT" if terminal_ok else "OPEN_GAPS"

payload=json.dumps(report,indent=2,sort_keys=True)
(OUT/"dependency_report.json").write_text(payload+"\n")
(OUT/"open_gaps.json").write_text(json.dumps(blocked,indent=2,sort_keys=True)+"\n")
(OUT/"endpoint_states.json").write_text(json.dumps(states,indent=2,sort_keys=True)+"\n")
(OUT/"family_index.json").write_text(json.dumps(family_index,indent=2,sort_keys=True)+"\n")
sha=hashlib.sha256(payload.encode()).hexdigest()
(OUT/"ROOT_SHA256").write_text(sha+"\n")

print(f"FINAL_PROOF_MINER={report['terminal_status']}")
for ep in endpoints:
    print(f"{ep}: {states[ep]['state']}")
print(f"EVIDENCE_ROOT={sha}")
