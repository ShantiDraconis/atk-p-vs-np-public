# m-core-p-vs-np — branch `atk/p02-only-20261001`

Lean sources from the branch `atk/p02-only-20261001` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `3e1d9f3efc049f837ba60c3aed790a9025755173` (2026-10-01T16:14:20+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 47 — closed 7, conditional 0, open 0, proof error 5, not reached 32, no result 3.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `f59bb6d47bd8fe40889cf806a6d16d643a68eb218c495acc57d2a0389a4ee866`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p02-only-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01ExactBoundedCircuitProducer.encodeCircuit_ne_nil` | `lean/MCore/Real/P01ExactBoundedCircuitProducer.lean`:96 | fechado |
| `MCore.Real.P01MalformedPhysicalReject.one_step_of_successor` | `lean/MCore/Real/P01MalformedPhysicalReject.lean`:21 | nao_checado |
| `MCore.Real.P01MalformedPhysicalReject.short_source_reaches_reject` | `lean/MCore/Real/P01MalformedPhysicalReject.lean`:57 | erro |
| `MCore.Real.P01MalformedPhysicalReject.tagDecode_short_rejects_within_three` | `lean/MCore/Real/P01MalformedPhysicalReject.lean`:32 | erro |
| `MCore.Real.P01RawClosureFinal.acceptsWithin_iff_larger_of_halts` | `lean/MCore/Real/P01RawClosureFinal.lean`:136 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.canonical_source_at_unified` | `lean/MCore/Real/P01RawClosureFinal.lean`:445 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.checked_total_unified` | `lean/MCore/Real/P01RawClosureFinal.lean`:479 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.circuit_with_wrapper_le_unified` | `lean/MCore/Real/P01RawClosureFinal.lean`:126 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.core_none_nonempty_fail_closed` | `lean/MCore/Real/P01RawClosureFinal.lean`:215 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.exactTime_le_unified` | `lean/MCore/Real/P01RawClosureFinal.lean`:62 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.linear_four_le_cubic` | `lean/MCore/Real/P01RawClosureFinal.lean`:67 | nao_checado |
| `MCore.Real.P01RawClosureFinal.linear_seven_le_cubic` | `lean/MCore/Real/P01RawClosureFinal.lean`:89 | nao_checado |
| `MCore.Real.P01RawClosureFinal.malformed_source_fail_closed` | `lean/MCore/Real/P01RawClosureFinal.lean`:382 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.p01ConstructionGap_closed` | `lean/MCore/Real/P01RawClosureFinal.lean`:548 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.prepared_nonempty_raw_fail_closed` | `lean/MCore/Real/P01RawClosureFinal.lean`:161 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.rawCoreBudget_root_eq` | `lean/MCore/Real/P01RawClosureFinal.lean`:111 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.rawCore_with_wrapper_le_unified` | `lean/MCore/Real/P01RawClosureFinal.lean`:116 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.residual_nonempty_fail_closed` | `lean/MCore/Real/P01RawClosureFinal.lean`:266 | nao_alcancado |
| `MCore.Real.P01RawClosureFinal.unifiedVerifierTimeBound_poly` | `lean/MCore/Real/P01RawClosureFinal.lean`:56 | nao_alcancado |
| `MCore.Real.P01RawCoreFailure.decodeNat_eq_none_eq_replicate_true` | `lean/MCore/Real/P01RawCoreFailure.lean`:52 | erro |
| `MCore.Real.P01RawCoreFailure.disallowed_tag_reaches_raw_failure` | `lean/MCore/Real/P01RawCoreFailure.lean`:212 | erro |
| `MCore.Real.P01RawCoreFailure.one_loop_le_rawCoreBudget` | `lean/MCore/Real/P01RawCoreFailure.lean`:78 | fechado |
| `MCore.Real.P01RawCoreFailure.truncated_tag_reaches_raw_failure` | `lean/MCore/Real/P01RawCoreFailure.lean`:94 | fechado |
| `MCore.Real.P01RawCoreFailure.truncated_unary_reaches_raw_failure` | `lean/MCore/Real/P01RawCoreFailure.lean`:140 | erro |
| `MCore.Real.P01RawCoreFailure.two_loop_le_rawCoreBudget` | `lean/MCore/Real/P01RawCoreFailure.lean`:87 | fechado |
| `MCore.Real.P01RawCoreFailureRecursive.binary_prefix_then_raw_budget` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:62 | nao_alcancado |
| `MCore.Real.P01RawCoreFailureRecursive.checkedCircuitBudget_le_raw_local` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:36 | nao_alcancado |
| `MCore.Real.P01RawCoreFailureRecursive.decodeCore_none_reaches_raw_failure` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:118 | nao_alcancado |
| `MCore.Real.P01RawCoreFailureRecursive.rawAssignment_apply` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:33 | nao_alcancado |
| `MCore.Real.P01RawCoreFailureRecursive.tag_then_circuit_budget` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:95 | nao_alcancado |
| `MCore.Real.P01RawCoreFailureRecursive.tag_then_raw_budget` | `lean/MCore/Real/P01RawCoreFailureRecursive.lean`:49 | nao_alcancado |
| `MCore.Real.P02KleeneFirewall.inP_excludes_kleeneSATBridgeGap` | `lean/MCore/Real/P02KleeneFirewall.lean`:32 | fechado |
| `MCore.Real.P02KleeneFirewall.kleeneSATBridgeGap_is_material_lower_bound` | `lean/MCore/Real/P02KleeneFirewall.lean`:43 | fechado |
| `MCore.Real.P02KleeneFirewall.no_fixedPointRealizer_of_global_correctness` | `lean/MCore/Real/P02KleeneFirewall.lean`:14 | fechado |
| `MCore.Real.P02RecoveredTableauKernel.boundedExecCorrectness_of_tableauCompleteness` | `lean/MCore/Real/P02RecoveredTableauKernel.lean`:14 | nao_alcancado |
| `MCore.Real.P02RecoveredTableauKernel.declaredExecutionBits_sat_iff_declaredAccept` | `lean/MCore/Real/P02RecoveredTableauKernel.lean`:37 | nao_alcancado |
| `MCore.Real.P02RecoveredTableauKernel.declaredExecutionBits_sat_iff_of_tableauCompleteness` | `lean/MCore/Real/P02RecoveredTableauKernel.lean`:48 | nao_alcancado |
| `MCore.Real.P02RecoveredTableauKernel.tableauCompletenessOnly_closes_boundedExec` | `lean/MCore/Real/P02RecoveredTableauKernel.lean`:25 | nao_alcancado |
| `MCore.Real.P02TableauCompletenessFrontier.transitionsComplete_closes_boundedExec` | `lean/MCore/Real/P02TableauCompletenessFrontier.lean`:39 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.SemanticDiagonalWitness.fails` | `lean/MCore/Real/P02UniversalKernel.lean`:42 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.SemanticDiagonalWitness.mismatch` | `lean/MCore/Real/P02UniversalKernel.lean`:28 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.pointwiseSemanticDiagonal_closes_p02` | `lean/MCore/Real/P02UniversalKernel.lean`:96 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.semanticDiagonalFamily_closes_final` | `lean/MCore/Real/P02UniversalKernel.lean`:112 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.semanticDiagonalFamily_closes_lowerBound` | `lean/MCore/Real/P02UniversalKernel.lean`:61 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.semanticDiagonalFamily_closes_notInP` | `lean/MCore/Real/P02UniversalKernel.lean`:68 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.semanticDiagonalFamily_to_final_open_math` | `lean/MCore/Real/P02UniversalKernel.lean`:104 | nao_alcancado |
| `MCore.Real.P02UniversalKernel.semanticFamily_iff_pointwise` | `lean/MCore/Real/P02UniversalKernel.lean`:81 | nao_alcancado |
