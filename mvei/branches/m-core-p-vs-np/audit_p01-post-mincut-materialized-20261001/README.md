# m-core-p-vs-np — branch `audit/p01-post-mincut-materialized-20261001`

Lean sources from the branch `audit/p01-post-mincut-materialized-20261001` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `83f0f96d8acabd68a0bb4050380c7d07642692d6` (2026-10-01T18:10:37+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 8 — closed 4, conditional 0, open 0, proof error 2, not reached 2, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `4adc2646d0b0512c52cfdbcfbec85e93ec6afea78faed3d5056b6b2fb5cd8c79`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/audit_p01-post-mincut-materialized-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_injective` | `lean/MCore/Real/P02FiniteDescriptorInfiniteOrbit.lean`:57 | nao_alcancado |
| `MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_length_strictMono` | `lean/MCore/Real/P02FiniteDescriptorInfiniteOrbit.lean`:49 | nao_alcancado |
| `MCore.Real.P02OpenMathRouteFalsification.constantPairTimeBound_poly` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:41 | fechado |
| `MCore.Real.P02OpenMathRouteFalsification.constantPair_declared_total` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:55 | erro |
| `MCore.Real.P02OpenMathRouteFalsification.constantPair_false_rejects` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:72 | fechado |
| `MCore.Real.P02OpenMathRouteFalsification.constantPair_no_output_alignment` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:84 | fechado |
| `MCore.Real.P02OpenMathRouteFalsification.constantPair_true_accepts` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:78 | fechado |
| `MCore.Real.P02OpenMathRouteFalsification.initialRightPart_length` | `lean/MCore/Real/P02OpenMathRouteFalsification.lean`:162 | erro |
