# m-core-p-vs-np — branch `atk/p02-primitive-semantic-laws-20261001`

Lean sources from the branch `atk/p02-primitive-semantic-laws-20261001` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `17610b461142bbc683fc98622b020a25caedf681` (2026-10-01T20:23:44+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 16 — closed 10, conditional 0, open 2, proof error 4, not reached 0, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `e03d190d744e46325b18b69d96ff8a1a2e7e57e3dd20e081baef460be32f1c91`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p02-primitive-semantic-laws-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P02ConcreteCandidateFailure.discriminator_accepts_notTrue` | `lean/MCore/Real/P02ConcreteCandidateFailure.lean`:32 | erro |
| `MCore.Real.P02ConcreteCandidateFailure.discriminator_cannot_be_sat_realization` | `lean/MCore/Real/P02ConcreteCandidateFailure.lean`:69 | aberto-sorry |
| `MCore.Real.P02ConcreteCandidateFailure.discriminator_not_correctAt_notTrue` | `lean/MCore/Real/P02ConcreteCandidateFailure.lean`:46 | aberto-sorry |
| `MCore.Real.P02ConcreteCandidateFailure.failureWitness_incompatible_with_realization` | `lean/MCore/Real/P02ConcreteCandidateFailure.lean`:80 | fechado |
| `MCore.Real.P02ConcreteCandidateFailure.notTrue_not_sat` | `lean/MCore/Real/P02ConcreteCandidateFailure.lean`:24 | fechado |
| `MCore.Real.P02PrimitiveSemanticLaws.discriminator_has_no_literal_fixed_point` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:102 | erro |
| `MCore.Real.P02PrimitiveSemanticLaws.fixed_point_is_constant_encoding` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:35 | erro |
| `MCore.Real.P02PrimitiveSemanticLaws.fixed_point_length_three` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:49 | fechado |
| `MCore.Real.P02PrimitiveSemanticLaws.no_fixed_point_of_constant_semantics` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:57 | erro |
| `MCore.Real.P02PrimitiveSemanticLaws.semanticNegationBits_length_three` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:26 | fechado |
| `MCore.Real.P02PrimitiveSemanticLaws.semanticNegationBits_two_point_range` | `lean/MCore/Real/P02PrimitiveSemanticLaws.lean`:12 | fechado |
| `MCore.Real.P02SemanticAlignmentCountermodel.discriminator_accepts_constTrue` | `lean/MCore/Real/P02SemanticAlignmentCountermodel.lean`:68 | fechado |
| `MCore.Real.P02SemanticAlignmentCountermodel.discriminator_clock_total` | `lean/MCore/Real/P02SemanticAlignmentCountermodel.lean`:55 | fechado |
| `MCore.Real.P02SemanticAlignmentCountermodel.discriminator_halts_two` | `lean/MCore/Real/P02SemanticAlignmentCountermodel.lean`:41 | fechado |
| `MCore.Real.P02SemanticAlignmentCountermodel.discriminator_no_output_alignment` | `lean/MCore/Real/P02SemanticAlignmentCountermodel.lean`:74 | fechado |
| `MCore.Real.P02SemanticAlignmentCountermodel.discriminator_rejects_constFalse` | `lean/MCore/Real/P02SemanticAlignmentCountermodel.lean`:61 | fechado |
