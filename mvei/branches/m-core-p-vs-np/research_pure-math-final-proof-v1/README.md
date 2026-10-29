# m-core-p-vs-np — branch `research/pure-math-final-proof-v1`

Lean sources from the branch `research/pure-math-final-proof-v1` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `235a8c1b04a9301f0bb85a85645344b5bcee985f` (2026-09-20T09:04:03+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 15 — closed 13, conditional 0, open 0, proof error 1, not reached 1, no result 0.
* History: 44 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `f851014b0eb6077357903c403580a3ff88b5a14b153f5f3b267a9e284a8fcbb2`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/research_pure-math-final-proof-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.charToDigit_digitChar_decimal` | `lean/MCore/Real/CNFStructure.lean`:476 | fechado |
| `MCore.Real.parseNatChars_append_digit` | `lean/MCore/Real/CNFStructure.lean`:577 | fechado |
| `MCore.Real.parseNatChars_cons_digit` | `lean/MCore/Real/CNFStructure.lean`:516 | fechado |
| `MCore.Real.parseNatChars_cons_digit_seen` | `lean/MCore/Real/CNFStructure.lean`:522 | fechado |
| `MCore.Real.parseNatChars_digit_list` | `lean/MCore/Real/CNFStructure.lean`:594 | fechado |
| `MCore.Real.parseNatChars_digit_tail` | `lean/MCore/Real/CNFStructure.lean`:585 | fechado |
| `MCore.Real.parseNatChars_single_digit` | `lean/MCore/Real/CNFStructure.lean`:511 | fechado |
| `MCore.Real.parseNatChars_toDigitsCore_terminal` | `lean/MCore/Real/CNFStructure.lean`:529 | fechado |
| `MCore.Real.toDigitsCore_decimal_decreases` | `lean/MCore/Real/CNFStructure.lean`:553 | fechado |
| `MCore.Real.toDigitsCore_decimal_mod_lt` | `lean/MCore/Real/CNFStructure.lean`:570 | fechado |
| `MCore.Real.toDigitsCore_decimal_step` | `lean/MCore/Real/CNFStructure.lean`:542 | fechado |
| `MCore.Real.toDigitsCore_decimal_step_decreases` | `lean/MCore/Real/CNFStructure.lean`:560 | fechado |
| `MCore.Real.toDigitsFoldRoundtrip_target` | `lean/MCore/Real/CNFStructure.lean`:635 | erro |
| `MCore.Real.toDigits_unfold` | `lean/MCore/Real/CNFStructure.lean`:472 | fechado |
| `MCore.Research.return_to_primary` | `lean/MCore/Research/ParallelClosure.lean`:12 | nao_alcancado |
