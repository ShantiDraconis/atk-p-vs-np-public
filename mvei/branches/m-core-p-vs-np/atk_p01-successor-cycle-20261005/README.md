# m-core-p-vs-np — branch `atk/p01-successor-cycle-20261005`

Lean sources from the branch `atk/p01-successor-cycle-20261005` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `e40ff6f5d4bf7c2d4a0e41b700185bf0be7429fd` (2026-10-09T00:38:46+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 67 — closed 65, conditional 0, open 0, proof error 2, not reached 0, no result 0.
* History: 103 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `2d42a2ae7b3f521e80ef53557dfbab5f5b7bedde08f0df7559c97faafb6c9d5e`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p01-successor-cycle-20261005/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.IntegratedMaterialProofs.arbitrary_encoder_sat_lower_bound_impossible` | `lean/MCore/Real/IntegratedMaterialProofs.lean`:30 | erro |
| `MCore.Real.IntegratedMaterialProofs.p01_of_material_machine` | `lean/MCore/Real/IntegratedMaterialProofs.lean`:17 | erro |
| `MCore.Real.IntegratedMaterialProofs.separation_of_material_witness` | `lean/MCore/Real/IntegratedMaterialProofs.lean`:23 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalRead_not_halting` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:29 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalRead_selected_step` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:176 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBitsConfig_state` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:113 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBits_marker_step` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:167 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBits_not_halting` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:26 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBits_run` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:143 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBits_step_cons` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:133 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBlanksConfig_state` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:42 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBlanks_first_bit_step` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:119 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBlanks_not_halting` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:23 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBlanks_run_to_first_bit` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:67 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.finalSeekBlanks_step_succ` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:57 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.final_indexSome_zero_step` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:47 | fechado |
| `MCore.Real.P01PreservingUnaryFinalRead.preservingRead_final_select` | `lean/MCore/Real/P01PreservingUnaryFinalRead.lean`:187 | fechado |
| `MCore.Real.P01PreservingUnaryIteration.iteratedCycleFuel_cons` | `lean/MCore/Real/P01PreservingUnaryIteration.lean`:25 | fechado |
| `MCore.Real.P01PreservingUnaryIteration.iteratedCycleFuel_nil` | `lean/MCore/Real/P01PreservingUnaryIteration.lean`:21 | fechado |
| `MCore.Real.P01PreservingUnaryIteration.preservingRead_iterated_cycles` | `lean/MCore/Real/P01PreservingUnaryIteration.lean`:32 | fechado |
| `MCore.Real.P01PreservingUnaryReaderClose.reader_certificate` | `lean/MCore/Real/P01PreservingUnaryReaderClose.lean`:66 | fechado |
| `MCore.Real.P01PreservingUnaryReaderClose.reader_exact_material` | `lean/MCore/Real/P01PreservingUnaryReaderClose.lean`:23 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.cleanupScanConfig_state_false` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:122 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.cleanupScanConfig_state_true` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:127 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.cleanup_scan_run` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:157 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.preservingRead_rewind_cleanup` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:241 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.preserving_not_halt_cleanupFalse` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:132 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.preserving_not_halt_cleanupTrue` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:135 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewindActive_state_false` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:34 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewindActive_state_true` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:38 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewind_all_active` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:85 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewind_done_enter_cleanup` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:147 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewind_one_cell_last` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:73 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.rewind_one_cell_more` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:62 | fechado |
| `MCore.Real.P01PreservingUnaryRewind.selected_to_rewind_active` | `lean/MCore/Real/P01PreservingUnaryRewind.lean`:42 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.forwardPhase_run` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:373 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.indexSome_true_step` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:54 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.preservingRead_indexSome_one_cycle` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:595 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.preserving_not_halt_returnBits` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:218 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.preserving_not_halt_returnBlanks` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:306 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.preserving_not_halt_seekBits` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:15 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.preserving_not_halt_seekBlanks` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:12 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.replicate_none_push` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:36 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.replicate_two_more_none` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:45 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBitsConfig_as_scan` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:231 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBitsScanConfig_state` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:211 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBits_blank_to_returnBlanks` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:346 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBits_run` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:244 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBits_step_cons` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:221 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanksScanConfig_state` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:300 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanks_run` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:319 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanks_step_succ` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:309 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanks_to_indexSome` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:358 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.returnPhase_run` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:500 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBitsConfig_state` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:124 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_marker_step` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:171 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_run` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:263 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_step_cons` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:144 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanksConfig_state` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:31 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_first_bit_step` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:130 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_run_to_first_bit` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:74 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_step_succ` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:65 | fechado |
| `MCore.Real.P01PreservingUnarySuccessorCycle.shift_carry_return_run_three` | `lean/MCore/Real/P01PreservingUnarySuccessorCycle.lean`:180 | fechado |
| `MCore.Real.P01PreservingUnaryUniversalRun.iteratedCycleFuel_closed_local` | `lean/MCore/Real/P01PreservingUnaryUniversalRun.lean`:43 | fechado |
| `MCore.Real.P01PreservingUnaryUniversalRun.preservingRead_nonzero_exact` | `lean/MCore/Real/P01PreservingUnaryUniversalRun.lean`:60 | fechado |
| `MCore.Real.P01PreservingUnaryUniversalRun.preservingRead_nonzero_material` | `lean/MCore/Real/P01PreservingUnaryUniversalRun.lean`:148 | fechado |
| `MCore.Real.P01PreservingUnaryUniversalRun.witness_split_at_index` | `lean/MCore/Real/P01PreservingUnaryUniversalRun.lean`:16 | fechado |
