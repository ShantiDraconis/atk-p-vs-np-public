# m-core-p-vs-np — branch `atk/p01-exact-rebuild-clean-20260930`

Lean sources from the branch `atk/p01-exact-rebuild-clean-20260930` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `565de3732aa3b7c2feb3d2ed9b86b0a0bb6a6c94` (2026-10-01T01:49:46+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 39 — closed 2, conditional 0, open 0, proof error 4, not reached 33, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `f3836340dcca8600992423e444f8281764e7ef990170f9dc16cfcb0764679c6c`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p01-exact-rebuild-clean-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01ExactBoundedCircuitProducer.binary_final_budget_eq` | `lean/MCore/Real/P01ExactBoundedCircuitProducer.lean`:123 | erro |
| `MCore.Real.P01ExactBoundedCircuitProducer.binary_prefix_budget_eq` | `lean/MCore/Real/P01ExactBoundedCircuitProducer.lean`:110 | erro |
| `MCore.Real.P01ExactBoundedCircuitProducer.loop_plus_budget_eq` | `lean/MCore/Real/P01ExactBoundedCircuitProducer.lean`:101 | erro |
| `MCore.Real.P01RawDecodeClassification.canonical_is_exact_encoding` | `lean/MCore/Real/P01RawDecodeClassification.lean`:44 | fechado |
| `MCore.Real.P01RawDecodeFailureCases.decodeCircuitCore_none_cases` | `lean/MCore/Real/P01RawDecodeFailureCases.lean`:53 | erro |
| `MCore.Real.P01RawDecodeFailureCases.inputUnary_payload_all_true` | `lean/MCore/Real/P01RawDecodeFailureCases.lean`:120 | fechado |
| `MCore.Real.P01RawMalformedBaseProducer.frame_length_le_of_layout` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:82 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.invalid_tag_reaches_fail_closed` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:128 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.loopEnvelope_le_rawMalformedSlice` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:31 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.n_le_loopEnvelope` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:65 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.short_reaches_fail_closed` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:96 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.slice_le_rawMalformedBudget` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:56 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.source_length_le_of_layout` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:89 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.two_loopEnvelope_le_rawMalformedSlice` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:43 | nao_alcancado |
| `MCore.Real.P01RawMalformedBaseProducer.unary_reaches_fail_closed` | `lean/MCore/Real/P01RawMalformedBaseProducer.lean`:172 | nao_alcancado |
| `MCore.Real.P01RawMalformedProducer.rawMalformedPhysicalProducer` | `lean/MCore/Real/P01RawMalformedProducer.lean`:20 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.and_left_failure` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:203 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.disallowed_root_fail_closed` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:36 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.neg_child_failure` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:170 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.or_left_failure` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:239 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.push_tag_then_recursive_fail_closed` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:69 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveLeft.slice_add_child_budget` | `lean/MCore/Real/P01RawMalformedRecursiveLeft.lean`:29 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveRight.and_right_failure` | `lean/MCore/Real/P01RawMalformedRecursiveRight.lean`:95 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveRight.checkedCircuitBudget_plus_one_loop_le_slice` | `lean/MCore/Real/P01RawMalformedRecursiveRight.lean`:78 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveRight.checkedCircuitBudget_plus_two_loops_le_slice` | `lean/MCore/Real/P01RawMalformedRecursiveRight.lean`:32 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveRight.local_slice_plus_child_budget` | `lean/MCore/Real/P01RawMalformedRecursiveRight.lean`:89 | nao_alcancado |
| `MCore.Real.P01RawMalformedRecursiveRight.or_right_failure` | `lean/MCore/Real/P01RawMalformedRecursiveRight.lean`:358 | nao_alcancado |
| `MCore.Real.P01RawMalformedVerifier.circuitBudget_le_rawSlice` | `lean/MCore/Real/P01RawMalformedVerifier.lean`:33 | nao_alcancado |
| `MCore.Real.P01RawMalformedVerifier.rawSlice_le_topBudget` | `lean/MCore/Real/P01RawMalformedVerifier.lean`:42 | nao_alcancado |
| `MCore.Real.P01RawMalformedVerifier.raw_malformed_reject_bounded` | `lean/MCore/Real/P01RawMalformedVerifier.lean`:46 | nao_alcancado |
| `MCore.Real.P01RawTotalContract.decodeCore_success_prefix` | `lean/MCore/Real/P01RawTotalContract.lean`:44 | nao_alcancado |
| `MCore.Real.P01RawTotalContract.decoded_prefix_length_le` | `lean/MCore/Real/P01RawTotalContract.lean`:55 | nao_alcancado |
| `MCore.Real.P01RawTotalContract.decoded_varBound_le_witness` | `lean/MCore/Real/P01RawTotalContract.lean`:63 | nao_alcancado |
| `MCore.Real.P01RawTotalContract.parsed_prefix_exact_dichotomy` | `lean/MCore/Real/P01RawTotalContract.lean`:85 | nao_alcancado |
| `MCore.Real.P01RawTotalContract.witnessAssignment_agrees` | `lean/MCore/Real/P01RawTotalContract.lean`:76 | nao_alcancado |
| `MCore.Real.P01RawVerifierFailClosed.lifted_explicit_reject_halted` | `lean/MCore/Real/P01RawVerifierFailClosed.lean`:24 | nao_alcancado |
| `MCore.Real.P01RawVerifierFailClosed.lifted_explicit_reject_not_accepting` | `lean/MCore/Real/P01RawVerifierFailClosed.lean`:36 | nao_alcancado |
| `MCore.Real.P01RawVerifierFailClosed.prepared_empty_fail_closed` | `lean/MCore/Real/P01RawVerifierFailClosed.lean`:109 | nao_alcancado |
| `MCore.Real.P01RawVerifierFailClosed.prepared_nonempty_eval_fail_closed` | `lean/MCore/Real/P01RawVerifierFailClosed.lean`:46 | nao_alcancado |
