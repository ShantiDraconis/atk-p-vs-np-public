# m-core-p-vs-np — branch `work/C9-two-channel-bridge`

Lean sources from the branch `work/C9-two-channel-bridge` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `5f1a10fa4f12d49835c1da5c22ade02dd687d9c9` (2026-09-18T02:32:00+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 29 — closed 1, conditional 0, open 2, proof error 6, not reached 20, no result 0.
* History: 9 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `5436e6a8882fe967e9022057bdae2409db02cfad67638ab7cf4980a4847bd1a7`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/work_C9-two-channel-bridge/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.C9.C9_TWO_CHANNEL_BRIDGE` | `lean/MCore/C9/TwoChannelCertificate.lean`:5 | nao_alcancado |
| `MCore.C9.GOOD0_STRICT_VAR_DESCENT` | `lean/MCore/C9/TwoChannelCertificate.lean`:10 | nao_alcancado |
| `MCore.C9.REFUTED_SINGLE_CHANNEL` | `lean/MCore/C9/TwoChannelCertificate.lean`:14 | nao_alcancado |
| `MCore.C9.allNone_not_good` | `lean/MCore/C9/RestrictionMass.lean`:38 | nao_alcancado |
| `MCore.C9.c9_endpoint_not_promoted` | `lean/MCore/C9/TwoChannelCertificate.lean`:20 | nao_alcancado |
| `MCore.C9.finiteGood_card` | `lean/MCore/C9/RestrictionMass.lean`:46 | nao_alcancado |
| `MCore.C9.finiteRestriction_card` | `lean/MCore/C9/RestrictionMass.lean`:10 | nao_alcancado |
| `MCore.C9.fixed_not_mem_D` | `lean/MCore/C9/FreeVars.lean`:88 | aberto-sorry |
| `MCore.C9.fixed_not_mem_restrict` | `lean/MCore/C9/FreeVars.lean`:35 | erro |
| `MCore.C9.freeVarSet_D_subset` | `lean/MCore/C9/FreeVars.lean`:95 | erro |
| `MCore.C9.good0_deltaN_pos` | `lean/MCore/C9/Progress.lean`:21 | nao_alcancado |
| `MCore.C9.good0_iff_touches` | `lean/MCore/C9/Good0.lean`:22 | nao_alcancado |
| `MCore.C9.good0_two_channel_progress` | `lean/MCore/C9/Progress.lean`:26 | nao_alcancado |
| `MCore.C9.good0_vars_strict` | `lean/MCore/C9/Progress.lean`:10 | nao_alcancado |
| `MCore.C9.goodFinset_compl_eq_singleton` | `lean/MCore/C9/RestrictionMass.lean`:41 | nao_alcancado |
| `MCore.C9.goodMass_four` | `lean/MCore/C9/RestrictionMass.lean`:67 | nao_alcancado |
| `MCore.C9.goodMass_one` | `lean/MCore/C9/RestrictionMass.lean`:64 | nao_alcancado |
| `MCore.C9.goodMass_three` | `lean/MCore/C9/RestrictionMass.lean`:66 | nao_alcancado |
| `MCore.C9.goodMass_two` | `lean/MCore/C9/RestrictionMass.lean`:65 | nao_alcancado |
| `MCore.C9.goodMass_zero` | `lean/MCore/C9/RestrictionMass.lean`:62 | nao_alcancado |
| `MCore.C9.mem_freeVarList_D` | `lean/MCore/C9/FreeVars.lean`:83 | aberto-sorry |
| `MCore.C9.mem_freeVarList_restrict` | `lean/MCore/C9/FreeVars.lean`:17 | fechado |
| `MCore.C9.mem_freeVarList_simplify` | `lean/MCore/C9/FreeVars.lean`:54 | erro |
| `MCore.C9.mem_freeVarSet` | `lean/MCore/C9/FreeVars.lean`:10 | erro |
| `MCore.C9.not_finiteGood_iff` | `lean/MCore/C9/RestrictionMass.lean`:23 | nao_alcancado |
| `MCore.C9.single_channel_counterexample` | `lean/MCore/C9/Progress.lean`:34 | nao_alcancado |
| `MCore.C9.touchesVars_not_const` | `lean/MCore/C9/Good0.lean`:17 | nao_alcancado |
| `MCore.C9.vars_D_le` | `lean/MCore/C9/FreeVars.lean`:100 | erro |
| `MCore.C9.vars_eq_card` | `lean/MCore/C9/FreeVars.lean`:14 | erro |
