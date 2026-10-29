# MVEI kernel check — m-core-p-vs-np

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/m-core-p-vs-np`. The sources are published in [`imports/m-core-p-vs-np/`](../imports/m-core-p-vs-np/).

## What is published

* Source: `ShantiDraconis/m-core-p-vs-np`, commit `328cb6726222af4ad93e7727737d477640f74f89` (2026-10-11T23:07:41Z).
* 150 files: 145 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material).
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-29T01:06:09+00:00, on commit `328cb6726222af4ad93e7727737d477640f74f89`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | OK | 1 141 | 0 | 0 | 145 / 0 / 0 / 0 / 507 |
| `atk-kernel` | v4.34.1 | OK | 2 | 0 | 0 | — |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 1 288 |
| Unique (name + statement) | 1 288 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 737 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

### Declared theorems

The `.lean` files of the verified commit declare 1 162 `theorem`/`lemma` (counting copies). The kernel checked 827 of them (827 closed, 0 conditional, 0 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 335 the kernel has no result:

| Reason | Theorems |
|---|---:|
| the project built, but the file is not part of the lakefile target | 200 |
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 135 |

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 6 file(s)): applies to the published sources: `git apply -p1 --directory=imports/m-core-p-vs-np mvei/correcoes/imports-no-topo.patch` (in order, after the ones above)

## Files in this folder

* `VERIFICACAO.json` — each Lean project of this repository, each theorem the kernel read, its statement, its axioms and its state (`fechado` closed, `condicional` conditional, `aberto-sorry` open)
* `TEOREMAS.csv` — each declared `theorem`/`lemma`: file, line, state in the kernel (`nao_checado` = not checked) and, if not checked, why (in Portuguese)
* `BUILD_LOG.txt` — one block per project: Lean version, result, errors
* `SOURCE.json` — source commit, verified commit and dates, machine-readable
* `SOURCES.sha256` — SHA-256 of every published file

## Reproduce

```
cd imports/m-core-p-vs-np/<project>   # a project folder from the table above ('.' is imports/m-core-p-vs-np)
lake exe cache get           # only for projects that require Mathlib
lake build
```

Each project uses the Lean version in its own `lean-toolchain`, which elan installs. The MVEI pipeline that produced these results is in the author's repository and is not public.
