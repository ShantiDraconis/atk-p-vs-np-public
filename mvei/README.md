# MVEI kernel check — m-core-p-vs-np

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/m-core-p-vs-np`. The sources are published in [`imports/m-core-p-vs-np/`](../imports/m-core-p-vs-np/).

## What is published

* Source: `ShantiDraconis/m-core-p-vs-np`, commit `328cb6726222af4ad93e7727737d477640f74f89` (2026-10-11T23:07:41Z).
* 150 files: 145 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material).
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-11-11T21:46:03+00:00, on commit `328cb6726222af4ad93e7727737d477640f74f89`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | partial | 1 601 | 0 | 0 | 72 / 0 / 6 / 47 / 4 |
| `atk-kernel` | v4.34.1 | OK | 2 | 0 | 0 | — |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 1 675 |
| Unique (name + statement) | 1 649 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 922 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `MCore.FinalFail.boundaryAtom_nonempty` | `. (file by file)` | open | `sorryAx` |
| `MCore.FinalFail.interpretedBoundary_nonempty` | `. (file by file)` | open | `sorryAx` |
| `MCore.FinalFail.nonempty_boundaryInterpretation_iff_nonempty_target` | `. (file by file)` | open | `sorryAx` |
| `MCore.FinalFail.boundaryAtom_nonempty` | `. (file by file)` | open | `sorryAx` |
| `MCore.FinalFail.interpretedBoundary_nonempty` | `. (file by file)` | open | `sorryAx` |
| `MCore.FinalFail.nonempty_boundaryInterpretation_iff_nonempty_target` | `. (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 1 162 `theorem`/`lemma` (counting copies). The kernel checked 1 046 of them (1 046 closed, 0 conditional, 0 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 116 the kernel has no result:

| Reason | Theorems |
|---|---:|
| the file did not compile (an error in it or in a file it imports) | 116 |

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 1 file(s)): applies to the published sources: `git apply -p1 --directory=imports/m-core-p-vs-np mvei/correcoes/imports-no-topo.patch` (in order, after the ones above)
* `correcoes/vocabulario-lean4.patch` (grafia que o Lean 4 não lê (nome acentuado, λ/Σ/Π como nome, ∀ x y ∈ s, docstring solta, constant, tática do Mathlib sem import), 73 file(s)): applies to the published sources: `git apply -p1 --directory=imports/m-core-p-vs-np mvei/correcoes/vocabulario-lean4.patch` (in order, after the ones above)
* `correcoes/z-provas-reparadas.patch` (prova que não passava no kernel (o enunciado fica igual), 3 file(s)): applies to the published sources: `git apply -p1 --directory=imports/m-core-p-vs-np mvei/correcoes/z-provas-reparadas.patch` (in order, after the ones above)

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
