# m-core-p-vs-np — branch `work/C12-progress-coverage`

Lean sources from the branch `work/C12-progress-coverage` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `f25fdb788277308961f956d7fad5709562d39c19` (2026-09-18T04:01:38+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 29 — closed 29, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 8 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `83827352210be3561df10fde3d25e4e0536da2a259e4546f1ba124ed075a32c5`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/work_C12-progress-coverage/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.C11.eraseDups_length_le_of_subset` | `lean/MCore/C11/VarsMonotone.lean`:126 | fechado |
| `MCore.C11.eraseDups_loop_mem_nat` | `lean/MCore/C11/VarsMonotone.lean`:10 | fechado |
| `MCore.C11.eraseDups_loop_nodup_nat` | `lean/MCore/C11/VarsMonotone.lean`:61 | fechado |
| `MCore.C11.eraseDups_nodup_nat` | `lean/MCore/C11/VarsMonotone.lean`:93 | fechado |
| `MCore.C11.mem_eraseDups_nat` | `lean/MCore/C11/VarsMonotone.lean`:89 | fechado |
| `MCore.C11.mem_freeVarList_D` | `lean/MCore/C11/VarsMonotone.lean`:253 | fechado |
| `MCore.C11.mem_freeVarList_reduceAnd` | `lean/MCore/C11/VarsMonotone.lean`:197 | fechado |
| `MCore.C11.mem_freeVarList_reduceNot` | `lean/MCore/C11/VarsMonotone.lean`:189 | fechado |
| `MCore.C11.mem_freeVarList_reduceOr` | `lean/MCore/C11/VarsMonotone.lean`:206 | fechado |
| `MCore.C11.mem_freeVarList_restrict` | `lean/MCore/C11/VarsMonotone.lean`:136 | fechado |
| `MCore.C11.mem_freeVarList_simplify` | `lean/MCore/C11/VarsMonotone.lean`:215 | fechado |
| `MCore.C11.nodup_length_le_of_subset_nat` | `lean/MCore/C11/VarsMonotone.lean`:97 | fechado |
| `MCore.C11.restrictionProgress_of_strict` | `lean/MCore/C11/VarsMonotone.lean`:281 | fechado |
| `MCore.C11.simplify_and_eq` | `lean/MCore/C11/VarsMonotone.lean`:183 | fechado |
| `MCore.C11.simplify_not_eq` | `lean/MCore/C11/VarsMonotone.lean`:180 | fechado |
| `MCore.C11.simplify_or_eq` | `lean/MCore/C11/VarsMonotone.lean`:186 | fechado |
| `MCore.C11.stateRank_D_decreases_of_strict` | `lean/MCore/C11/VarsMonotone.lean`:287 | fechado |
| `MCore.C11.varsNonincrease_closed` | `lean/MCore/C11/VarsMonotone.lean`:272 | fechado |
| `MCore.C11.vars_D_le` | `lean/MCore/C11/VarsMonotone.lean`:263 | fechado |
| `MCore.C12.eraseDups_length_lt_of_subset_of_missing` | `lean/MCore/C12/ProgressCoverage.lean`:49 | fechado |
| `MCore.C12.exists_freeVar_of_vars_pos` | `lean/MCore/C12/ProgressCoverage.lean`:78 | fechado |
| `MCore.C12.exists_rank_decreasing_restriction` | `lean/MCore/C12/ProgressCoverage.lean`:122 | fechado |
| `MCore.C12.fixVarTrue_ne` | `lean/MCore/C12/ProgressCoverage.lean`:16 | fechado |
| `MCore.C12.fixVarTrue_self` | `lean/MCore/C12/ProgressCoverage.lean`:12 | fechado |
| `MCore.C12.fixedVar_not_mem_D` | `lean/MCore/C12/ProgressCoverage.lean`:40 | fechado |
| `MCore.C12.fixedVar_not_mem_restrict` | `lean/MCore/C12/ProgressCoverage.lean`:20 | fechado |
| `MCore.C12.progressCoverage_closed` | `lean/MCore/C12/ProgressCoverage.lean`:112 | fechado |
| `MCore.C12.strictProgress_fix_present` | `lean/MCore/C12/ProgressCoverage.lean`:105 | fechado |
| `MCore.C12.vars_D_lt_fixVarTrue` | `lean/MCore/C12/ProgressCoverage.lean`:92 | fechado |
