# ATK P-VS-NP — Formal Research

Research repository maintained by Tiago Paschoalatto Fagliari (ORCID: https://orcid.org/0009-0006-6874-3910).

Status: **research in progress; no unconditional solution or Millennium Prize certification is claimed.**

This repository will preserve source paths, original commit SHAs, authorship, dependencies, and exact Lean verification outcomes. A successful Lean build does not by itself prove an original open problem unless the formalized theorem exactly matches it and all assumptions are discharged.

Related publication: https://doi.org/10.5281/zenodo.15164501 (historical publication; not a proof certificate).

Do not add confidential data or third-party code without checking its license and attribution.

<!-- mvei:start -->
## Lean sources and kernel check (MVEI)

[`imports/m-core-p-vs-np/`](imports/m-core-p-vs-np/) holds the Lean sources of `ShantiDraconis/m-core-p-vs-np` at commit `328cb67` (2026-10-11): 150 files. In the MVEI verification the Lean kernel closed 1 143 theorems here (592 unique, without the lemmas Lean generates itself), with 0 conditional and 0 open (`sorry`). A closed theorem proves the statement written in the file; it is not a claim that an open problem is solved. Statements, axioms, the build log and how to reproduce: [`mvei/README.md`](mvei/README.md).
<!-- mvei:end -->
