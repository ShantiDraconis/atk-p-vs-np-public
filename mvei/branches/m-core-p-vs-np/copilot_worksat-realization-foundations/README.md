# m-core-p-vs-np — branch `copilot/worksat-realization-foundations`

Lean sources from the branch `copilot/worksat-realization-foundations` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `a16918d8ff2a9b35a25bd963686155b81d8496f8` (2026-09-19T16:48:47+00:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 22 — closed 2, conditional 0, open 11, proof error 4, not reached 0, no result 5.
* History: 1 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `d03dfad9bb042e65cac10e76dc065cea98a82750ea85b8ad23004aa692828d7f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/copilot_worksat-realization-foundations/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.SATNPRealization` | `lean/MCore/Real/SATRealization.lean`:368 | aberto-sorry |
| `MCore.Real.encodeCNF_injective` | `lean/MCore/Real/SATRealization.lean`:177 | erro |
| `MCore.Real.parseCNFList_encode` | `lean/MCore/Real/SATRealization.lean`:162 | nao_checado |
| `MCore.Real.parseCNF_encode` | `lean/MCore/Real/SATRealization.lean`:173 | aberto-sorry |
| `MCore.Real.parseCNF_negativeControl_badPrefix` | `lean/MCore/Real/SATRealization.lean`:192 | aberto-sorry |
| `MCore.Real.parseCNF_negativeControl_empty` | `lean/MCore/Real/SATRealization.lean`:190 | aberto-sorry |
| `MCore.Real.parseClause_encode` | `lean/MCore/Real/SATRealization.lean`:158 | nao_checado |
| `MCore.Real.parseLiteralList_encode` | `lean/MCore/Real/SATRealization.lean`:147 | nao_checado |
| `MCore.Real.parseLiteral_encode` | `lean/MCore/Real/SATRealization.lean`:139 | aberto-sorry |
| `MCore.Real.parseNatUnaryAux_replicate` | `lean/MCore/Real/SATRealization.lean`:127 | nao_checado |
| `MCore.Real.parseNatUnary_encode` | `lean/MCore/Real/SATRealization.lean`:134 | aberto-sorry |
| `MCore.Real.runBranches_two` | `lean/MCore/Real/SATRealization.lean`:271 | nao_checado |
| `MCore.Real.satRuntime_matches_two` | `lean/MCore/Real/SATRealization.lean`:358 | fechado |
| `MCore.Real.satRuntime_poly` | `lean/MCore/Real/SATRealization.lean`:353 | fechado |
| `MCore.Real.sat_acceptsWithin_two_of_language` | `lean/MCore/Real/SATRealization.lean`:281 | erro |
| `MCore.Real.sat_decidesWithin` | `lean/MCore/Real/SATRealization.lean`:360 | aberto-sorry |
| `MCore.Real.sat_language_of_acceptsWithin_two` | `lean/MCore/Real/SATRealization.lean`:290 | erro |
| `MCore.Real.sat_sound_complete` | `lean/MCore/Real/SATRealization.lean`:309 | aberto-sorry |
| `MCore.Real.sat_uniform_halting` | `lean/MCore/Real/SATRealization.lean`:315 | erro |
| `MCore.Real.semanticallyRepresents_exact` | `lean/MCore/Real/SATRealization.lean`:187 | aberto-sorry |
| `MCore.Real.wellFormed_exact` | `lean/MCore/Real/SATRealization.lean`:184 | aberto-sorry |
| `MCore.Real.wellFormed_of_encode` | `lean/MCore/Real/SATRealization.lean`:194 | aberto-sorry |
