# m-core-p-vs-np — branch `atk/p01-exact-consumption-certificate-20260930`

Lean sources from the branch `atk/p01-exact-consumption-certificate-20260930` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `a40c7bb1d05ac875bc9d9c0fb24a87b21d0e6805` (2026-10-01T01:22:13+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 9 — closed 3, conditional 0, open 0, proof error 1, not reached 3, no result 2.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `cfa41b40194417f9253dc6c57c72613b4a1b208c0b0d2c7e1103b2be322fecac`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_p01-exact-consumption-certificate-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01CheckedEvalBoundedOutcome.layout_of_frames_ne_nil` | `lean/MCore/Real/P01CheckedEvalBoundedOutcome.lean`:65 | fechado |
| `MCore.Real.P01CheckedEvalBoundedOutcome.layout_of_tail_ne_nil` | `lean/MCore/Real/P01CheckedEvalBoundedOutcome.lean`:48 | fechado |
| `MCore.Real.P01CheckedEvalBoundedOutcome.to_checked` | `lean/MCore/Real/P01CheckedEvalBoundedOutcome.lean`:40 | fechado |
| `MCore.Real.P01CheckedEvalRunBoundedBinary.and_bounded_certificate` | `lean/MCore/Real/P01CheckedEvalRunBoundedBinary.lean`:60 | nao_alcancado |
| `MCore.Real.P01CheckedEvalRunBoundedBinary.and_budget` | `lean/MCore/Real/P01CheckedEvalRunBoundedBinary.lean`:28 | nao_checado |
| `MCore.Real.P01CheckedEvalRunBoundedBinary.circuit_bounded_certificate` | `lean/MCore/Real/P01CheckedEvalRunBoundedBinary.lean`:711 | nao_alcancado |
| `MCore.Real.P01CheckedEvalRunBoundedBinary.or_bounded_certificate` | `lean/MCore/Real/P01CheckedEvalRunBoundedBinary.lean`:389 | nao_alcancado |
| `MCore.Real.P01CheckedEvalRunBoundedBinary.or_budget` | `lean/MCore/Real/P01CheckedEvalRunBoundedBinary.lean`:44 | nao_checado |
| `MCore.Real.P01CheckedEvalRunBoundedHelpers.have_reaches_bounded_outcome` | `lean/MCore/Real/P01CheckedEvalRunBoundedHelpers.lean`:191 | erro |
