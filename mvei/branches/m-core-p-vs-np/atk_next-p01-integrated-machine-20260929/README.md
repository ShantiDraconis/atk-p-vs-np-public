# m-core-p-vs-np — branch `atk/next-p01-integrated-machine-20260929`

Lean sources from the branch `atk/next-p01-integrated-machine-20260929` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `833fe0ded9676bfd19d226b8bf1dfd0aeb070bf5` (2026-09-29T10:12:45+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 16 — closed 4, conditional 0, open 0, proof error 0, not reached 12, no result 0.
* History: 13 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `b8da96b28810928d5c0547ea5d21151cd04c1bf8e5c7958c3828d8e196485e75`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_next-p01-integrated-machine-20260929/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01DeterministicNTMEmbedding.runBranches_halted_all` | `lean/MCore/Real/P01DeterministicNTMEmbedding.lean`:112 | fechado |
| `MCore.Real.P01DeterministicNTMEmbedding.runBranches_tmAsNTM_singleton` | `lean/MCore/Real/P01DeterministicNTMEmbedding.lean`:132 | fechado |
| `MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_acceptsWithin_iff` | `lean/MCore/Real/P01DeterministicNTMEmbedding.lean`:180 | fechado |
| `MCore.Real.P01DeterministicNTMEmbedding.tmHaltsWithin_iff_ntmHaltsWithin` | `lean/MCore/Real/P01DeterministicNTMEmbedding.lean`:159 | fechado |
| `MCore.Real.P01EvalFramePopMachine.framePop_empty_rejects` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:230 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_first_two` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:149 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_gap1_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:107 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_gap2_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:127 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_read0_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:97 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_read1_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:117 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_read2_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:137 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_run_six` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:199 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_second_two` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:166 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_start_one` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:87 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.framePop_third_two` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:182 | nao_alcancado |
| `MCore.Real.P01EvalFramePopMachine.tape_write_none_of_head_none` | `lean/MCore/Real/P01EvalFramePopMachine.lean`:77 | nao_alcancado |
