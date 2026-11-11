# m-core-p-vs-np — branch `atk/p01-raw-closure-unified-20261001`

Lean sources from the branch `atk/p01-raw-closure-unified-20261001` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `fc21c82a1b17e3330908c76b5d1e64a983f8499d` (2026-10-01T01:26:40+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 13 — closed 5, conditional 0, open 2, proof error 0, not reached 6, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `87e1ef57f6a05d7ffb6884892479e9d45e12161813e2f2ede100a5bae13da09d`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p01-raw-closure-unified-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01RawSourceClosure.acceptsWithin_iff_of_haltsWithin_mono` | `lean/MCore/Real/P01RawSourceClosure.lean`:346 | nao_alcancado |
| `MCore.Real.P01RawSourceClosure.checked_total` | `lean/MCore/Real/P01RawSourceClosure.lean`:397 | nao_alcancado |
| `MCore.Real.P01RawSourceClosure.exactTimeBound_le_raw` | `lean/MCore/Real/P01RawSourceClosure.lean`:55 | fechado |
| `MCore.Real.P01RawSourceClosure.lift_eval_raw_failure` | `lean/MCore/Real/P01RawSourceClosure.lean`:106 | fechado |
| `MCore.Real.P01RawSourceClosure.linear_le_cube_budget` | `lean/MCore/Real/P01RawSourceClosure.lean`:61 | fechado |
| `MCore.Real.P01RawSourceClosure.p01ConstructionGap_closed` | `lean/MCore/Real/P01RawSourceClosure.lean`:483 | aberto-sorry |
| `MCore.Real.P01RawSourceClosure.prepared_core_none_fail_closed` | `lean/MCore/Real/P01RawSourceClosure.lean`:172 | nao_alcancado |
| `MCore.Real.P01RawSourceClosure.prepared_empty_fail_closed` | `lean/MCore/Real/P01RawSourceClosure.lean`:85 | fechado |
| `MCore.Real.P01RawSourceClosure.prepared_residual_fail_closed` | `lean/MCore/Real/P01RawSourceClosure.lean`:225 | nao_alcancado |
| `MCore.Real.P01RawSourceClosure.rawSourceClosure` | `lean/MCore/Real/P01RawSourceClosure.lean`:373 | nao_alcancado |
| `MCore.Real.P01RawSourceClosure.rawSourceClosure_at_some_fuel` | `lean/MCore/Real/P01RawSourceClosure.lean`:319 | aberto-sorry |
| `MCore.Real.P01RawSourceClosure.rawVerifierTimeBound_poly` | `lean/MCore/Real/P01RawSourceClosure.lean`:51 | fechado |
| `MCore.Real.P01RawSourceClosure.root_rawCoreBudget_le` | `lean/MCore/Real/P01RawSourceClosure.lean`:78 | nao_alcancado |
