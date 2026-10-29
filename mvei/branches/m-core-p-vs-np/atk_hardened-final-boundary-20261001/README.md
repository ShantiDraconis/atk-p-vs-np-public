# m-core-p-vs-np — branch `atk/hardened-final-boundary-20261001`

Lean sources from the branch `atk/hardened-final-boundary-20261001` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `a72561ede8d806c2169a96f23510742f974f50f5` (2026-10-01T01:44:20+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 47 — closed 26, conditional 0, open 0, proof error 0, not reached 21, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `3d9fa992c5cd3e3cf7347f61793e9ee9d4bb7373bd25d83116f678fc5906de41`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_hardened-final-boundary-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.AutoCompose.extract` | `lean/MCore/AutoCompose.lean`:39 | fechado |
| `MCore.Real.CanonicalFinalExternal.FINAL_ROOT_of_p01_and_failure` | `lean/MCore/Real/CanonicalFinalExternal.lean`:51 | fechado |
| `MCore.Real.CanonicalFinalExternal.finalExternal_to_FINAL_ROOT` | `lean/MCore/Real/CanonicalFinalExternal.lean`:24 | fechado |
| `MCore.Real.CanonicalFinalExternal.minimalFinalExternal_to_FINAL_ROOT` | `lean/MCore/Real/MinimalFinalExternal.lean`:27 | nao_alcancado |
| `MCore.Real.CanonicalFinalExternal.minimalFinalExternal_to_OFFICIAL_ROOT` | `lean/MCore/Real/MinimalFinalExternal.lean`:37 | nao_alcancado |
| `MCore.Real.CanonicalFinalExternal.official_root_of_p01_failure_and_model_match` | `lean/MCore/Real/CanonicalFinalExternal.lean`:58 | fechado |
| `MCore.Real.CanonicalFinalExternal.p01Construction_of_verifier` | `lean/MCore/Real/MinimalFinalExternal.lean`:15 | nao_alcancado |
| `MCore.Real.CanonicalFinalExternal.p01_supplies_satInNP` | `lean/MCore/Real/CanonicalFinalExternal.lean`:32 | fechado |
| `MCore.Real.EncodedFinalProof.encodedSATInNP_of_P01Gap` | `lean/MCore/Real/EncodedFinalProof.lean`:118 | fechado |
| `MCore.Real.EncodedFinalProof.encoded_failure_implies_sat_not_in_p` | `lean/MCore/Real/EncodedFinalProof.lean`:77 | fechado |
| `MCore.Real.EncodedFinalProof.encoded_sat_boundary_implies_separation` | `lean/MCore/Real/EncodedFinalProof.lean`:85 | fechado |
| `MCore.Real.EncodedFinalProof.rigorousFinalExternal_to_ROOT` | `lean/MCore/Real/EncodedFinalProof.lean`:130 | fechado |
| `MCore.Real.FINAL_ROOT_of_sat_inputs` | `lean/MCore/Real/ExactFinalProducer.lean`:15 | fechado |
| `MCore.Real.FinalExternalCanonical.FINAL_ROOT` | `lean/MCore/Real/FinalExternalCanonical.lean`:44 | fechado |
| `MCore.Real.HardenedFinal.finalExternal_to_FINAL_ROOT` | `lean/MCore/Real/HardenedFinalExternal.lean`:38 | fechado |
| `MCore.Real.HardenedFinal.officialFinalExternal_to_root` | `lean/MCore/Real/HardenedFinalExternal.lean`:54 | fechado |
| `MCore.Real.HardenedFinal.p01_to_sat_in_np` | `lean/MCore/Real/HardenedFinalExternal.lean`:24 | fechado |
| `MCore.Real.HardenedFinalBoundary.exact_two_producers_to_final_root` | `lean/MCore/Real/HardenedFinalBoundary.lean`:75 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.exact_two_producers_to_official_root` | `lean/MCore/Real/HardenedFinalBoundary.lean`:85 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.final_external_no_escape_p01` | `lean/MCore/Real/HardenedFinalBoundary.lean`:55 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.final_external_no_escape_p02` | `lean/MCore/Real/HardenedFinalBoundary.lean`:62 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.final_external_nonempty_iff_p01_and_universal_failure` | `lean/MCore/Real/HardenedFinalBoundary.lean`:40 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.final_external_nonempty_iff_two_producers` | `lean/MCore/Real/HardenedFinalBoundary.lean`:18 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.final_external_yields_universal_failure` | `lean/MCore/Real/HardenedFinalBoundary.lean`:69 | nao_alcancado |
| `MCore.Real.HardenedFinalBoundary.p02_failure_generator_iff_universal_failure` | `lean/MCore/Real/HardenedFinalBoundary.lean`:36 | nao_alcancado |
| `MCore.Real.P01BitFinal.FINAL_ROOT_of_p01_and_fail` | `lean/MCore/Real/P01BitFinalExternal.lean`:48 | fechado |
| `MCore.Real.P01BitFinal.finalExternal_to_FINAL_ROOT` | `lean/MCore/Real/P01BitFinalExternal.lean`:24 | fechado |
| `MCore.Real.P01BitFinal.p01Construction_to_satInNP` | `lean/MCore/Real/P01BitFinalExternal.lean`:30 | fechado |
| `MCore.Real.P01CanonicalPolynomialClose.canonicalVerifierTimeBound_poly` | `lean/MCore/Real/P01CanonicalPolynomialClose.lean`:32 | nao_alcancado |
| `MCore.Real.P01CanonicalPolynomialClose.checkedCircuitBudget_le_cubic` | `lean/MCore/Real/P01CanonicalPolynomialClose.lean`:36 | nao_alcancado |
| `MCore.Real.P01CanonicalPolynomialClose.scan_prefix_le_cubic` | `lean/MCore/Real/P01CanonicalPolynomialClose.lean`:51 | nao_alcancado |
| `MCore.Real.P01CanonicalPolynomialClose.valid_cnf_reaches_terminal_within` | `lean/MCore/Real/P01CanonicalPolynomialClose.lean`:56 | nao_alcancado |
| `MCore.Real.P01ExactOrBounded.circuit_exact_bounded_certificate` | `lean/MCore/Real/P01ExactOrBounded.lean`:464 | nao_alcancado |
| `MCore.Real.P01ExactOrBounded.or_exact_bounded_certificate` | `lean/MCore/Real/P01ExactOrBounded.lean`:22 | nao_alcancado |
| `MCore.Real.P01VerifierResidual.p01ConstructionGap_of_physicalRejectResidual` | `lean/MCore/Real/P01VerifierResidualClose.lean`:87 | nao_alcancado |
| `MCore.Real.P01VerifierResidual.rawVerifier_halts_accepts_iff` | `lean/MCore/Real/P01VerifierResidualClose.lean`:16 | nao_alcancado |
| `MCore.Real.P01VerifierResidual.validCanonical_halts_accepts_iff` | `lean/MCore/Real/P01VerifierResidualCore.lean`:38 | nao_alcancado |
| `MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_gap_iff_pointwise` | `lean/MCore/Real/P02SemanticSelfEmbedding.lean`:85 | nao_alcancado |
| `MCore.Real.collapseSATCandidate_correctAt` | `lean/MCore/Real/CurrentModelCollapse.lean`:81 | fechado |
| `MCore.Real.collapseTimeBound_poly` | `lean/MCore/Real/CurrentModelCollapse.lean`:61 | fechado |
| `MCore.Real.finalExternalCertificate_to_FINAL_ROOT` | `lean/MCore/Real/FinalExternal.lean`:32 | fechado |
| `MCore.Real.finalExternal_iff_residual` | `lean/MCore/Real/FinalExternal.lean`:39 | fechado |
| `MCore.Real.finalExternal_to_FINAL_ROOT` | `lean/MCore/Real/FinalExternal.lean`:26 | fechado |
| `MCore.Real.finalExternal_to_residual` | `lean/MCore/Real/FinalExternal.lean`:20 | fechado |
| `MCore.Real.no_final_external_certificate_in_current_model` | `lean/MCore/Real/CurrentModelCollapse.lean`:119 | fechado |
| `MCore.Real.no_sat_lower_bound_certificate_in_current_model` | `lean/MCore/Real/CurrentModelCollapse.lean`:110 | fechado |
| `MCore.Real.sat_in_p_in_current_unrestricted_model` | `lean/MCore/Real/CurrentModelCollapse.lean`:106 | fechado |
