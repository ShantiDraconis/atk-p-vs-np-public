# m-core-p-vs-np — branch `attack/t1d-close-contract-20260922`

Lean sources from the branch `attack/t1d-close-contract-20260922` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `b28a549651d11d527e7097eb013f3fbd847eff21` (2026-09-22T17:29:41+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 2 — closed 2, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `c31df7d935733946ed0e23ef32840ddd8a1f9beb34fdab89b72d7d748dddad5b`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/attack_t1d-close-contract-20260922/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01T1DClosureContract.t1d_gap_decomposes` | `lean/MCore/Real/P01T1DClosureContract.lean`:37 | fechado |
| `MCore.Real.P01T1DClosureContract.t1d_package_closes_p01` | `lean/MCore/Real/P01T1DClosureContract.lean`:23 | fechado |
