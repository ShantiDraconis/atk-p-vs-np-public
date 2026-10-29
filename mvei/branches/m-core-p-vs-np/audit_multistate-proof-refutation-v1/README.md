# m-core-p-vs-np — branch `audit/multistate-proof-refutation-v1`

Lean sources from the branch `audit/multistate-proof-refutation-v1` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `01848759e400553769221813e5466ddacdae877e` (2026-09-19T10:39:32+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 36 — closed 16, conditional 0, open 0, proof error 19, not reached 1, no result 0.
* History: 28 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `3b029f8b39fe617f4ac0337e0a099a8344deda75cab7e16354a8480657a5f59f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/audit_multistate-proof-refutation-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `Audit.OfficialModel.F1_canonical_model_match` | `audit/OfficialModel/F1_OfficialModelMatch.lean`:28 | erro |
| `Audit.OfficialModel.F1_internal_to_official_NP` | `audit/OfficialModel/F1_OfficialModelMatch.lean`:23 | erro |
| `Audit.OfficialModel.F1_internal_to_official_P` | `audit/OfficialModel/F1_OfficialModelMatch.lean`:18 | erro |
| `Audit.OfficialModel.F2_implies_separation` | `audit/OfficialModel/F2_FixedWitness.lean`:15 | erro |
| `Audit.OfficialModel.halted_toNTM` | `audit/OfficialModel/OperationalTM.lean`:148 | fechado |
| `Audit.OfficialModel.lower_bound_witness_separates` | `audit/OfficialModel/F2_FixedWitness.lean`:10 | erro |
| `Audit.OfficialModel.nextConfigs_toNTM` | `audit/OfficialModel/OperationalTM.lean`:151 | fechado |
| `Audit.OfficialModel.ofOfficial_toOfficial` | `audit/OfficialModel/F1_OfficialModelMatch.lean`:15 | fechado |
| `Audit.OfficialModel.officialP_subset_officialNP` | `audit/OfficialModel/OperationalTM.lean`:165 | fechado |
| `Audit.OfficialModel.runSet_toNTM_singleton` | `audit/OfficialModel/OperationalTM.lean`:158 | fechado |
| `Audit.OfficialModel.toOfficial_ofOfficial` | `audit/OfficialModel/F1_OfficialModelMatch.lean`:12 | fechado |
| `Audit.SAT.SATBits_encodeCNF_iff` | `audit/SAT/SATNPRealization.lean`:49 | erro |
| `Audit.SAT.SATBits_iff_bitWitnessSemantics` | `audit/SAT/SATNPRealization.lean`:40 | erro |
| `Audit.SAT.SATEncodingExistence_closed` | `audit/SAT/SATEncoding.lean`:134 | erro |
| `Audit.SAT.SATNTMRealization_implies_OfficialNP` | `audit/SAT/SATNPRealization.lean`:81 | erro |
| `Audit.SAT.decodeCNF_encodeCNF` | `audit/SAT/SATEncoding.lean`:111 | erro |
| `Audit.SAT.decodeClause_encodeClause_append` | `audit/SAT/SATEncoding.lean`:93 | erro |
| `Audit.SAT.decodeList_encodeList_append` | `audit/SAT/SATEncoding.lean`:74 | erro |
| `Audit.SAT.decodeLiteral_encodeLiteral_append` | `audit/SAT/SATEncoding.lean`:32 | erro |
| `Audit.SAT.decodeN_encodeNList_append` | `audit/SAT/SATEncoding.lean`:51 | erro |
| `Audit.SAT.decodeNat_encodeNat_append` | `audit/SAT/SATEncoding.lean`:13 | erro |
| `Audit.SAT.decode_none_not_SATBits` | `audit/SAT/SATNPRealization.lean`:60 | erro |
| `Audit.SAT.sat_verifier_correct` | `audit/SAT/SATCore.lean`:33 | fechado |
| `Audit.SAT.satisfiable_iff_bitWitness` | `audit/SAT/SATNPRealization.lean`:23 | erro |
| `Audit.SAT.three_sat_implies_sat` | `audit/SAT/SATCore.lean`:49 | fechado |
| `Audit.SAT.valuationBits_length` | `audit/SAT/SATNPRealization.lean`:5 | erro |
| `Audit.SAT.valuationOfExactBits_valuationBits` | `audit/SAT/SATNPRealization.lean`:13 | erro |
| `Audit.SAT.witness_length_exact` | `audit/SAT/SATCore.lean`:40 | fechado |
| `MCore.Audit8x5.A_axis_pending` | `lean/MCore/Audit8x5.lean`:50 | fechado |
| `MCore.Audit8x5.HC_axis_blocking` | `lean/MCore/Audit8x5.lean`:45 | fechado |
| `MCore.Audit8x5.K_axis_blocking` | `lean/MCore/Audit8x5.lean`:49 | fechado |
| `MCore.Audit8x5.Q_axis_blocking` | `lean/MCore/Audit8x5.lean`:47 | fechado |
| `MCore.Audit8x5.S_axis_blocking` | `lean/MCore/Audit8x5.lean`:48 | fechado |
| `MCore.Audit8x5.no_placebo_classical_endpoint` | `lean/MCore/Audit8x5.lean`:20 | fechado |
| `MCore.Audit8x5.no_placebo_k10` | `lean/MCore/Audit8x5.lean`:28 | fechado |
| `MultistateAudit.PvsNP.Gates.fullyAudited_elim` | `audit/20_BACKWARD_ELIMINATION/MassiveGateArchitecture.lean`:34 | nao_alcancado |
