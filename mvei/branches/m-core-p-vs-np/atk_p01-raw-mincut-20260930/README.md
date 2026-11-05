# m-core-p-vs-np — branch `atk/p01-raw-mincut-20260930`

Lean sources from the branch `atk/p01-raw-mincut-20260930` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `4af7e2c3c9886c0d11c7f3c16f00f7dd671c61d5` (2026-10-01T00:11:12+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 1, conditional 0, open 2, proof error 1, not reached 0, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `5f0cde9493563a67b75e6f17bb572f3606e907d3ef068ff694421c3d182f5dc1`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p01-raw-mincut-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01RawSourceSplit.exact_encoding_of_slotAccept` | `lean/MCore/Real/P01RawSourceSplit.lean`:37 | fechado |
| `MCore.Real.P01RawSourceSplit.slotReject_iff_no_exact_encoding` | `lean/MCore/Real/P01RawSourceSplit.lean`:44 | erro |
| `MCore.Real.P01VerifierPhaseMinCut.checked_total_of_raw_source_closure` | `lean/MCore/Real/P01VerifierPhaseMinCut.lean`:56 | aberto-sorry |
| `MCore.Real.P01VerifierPhaseMinCut.p01ConstructionGap_of_rawSourceClosure` | `lean/MCore/Real/P01VerifierPhaseMinCut.lean`:126 | aberto-sorry |
