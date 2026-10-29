# m-core-p-vs-np — branch `atk/next-pnp-finite-clock-explicit-coding-20260928`

Lean sources from the branch `atk/next-pnp-finite-clock-explicit-coding-20260928` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `f6fcff38d32a6ac49cf9eb1d61640418fa84d8a8` (2026-09-28T22:24:07+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 43 — closed 20, conditional 0, open 0, proof error 0, not reached 23, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `706e9b69875a3df1a5cefb6e178cb01d13aa1864e553ef1cf46c6ac4e1eec64f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_next-pnp-finite-clock-explicit-coding-20260928/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.CookNormalizedOfficialBinding.canonical_inNP_iff_cook_normalized_NP` | `lean/MCore/Real/CookNormalizedOfficialBinding.lean`:31 | nao_alcancado |
| `MCore.Real.CookNormalizedOfficialBinding.canonical_inP_iff_cook_normalized_P` | `lean/MCore/Real/CookNormalizedOfficialBinding.lean`:22 | nao_alcancado |
| `MCore.Real.CookNormalizedOfficialBinding.canonical_interface_bound_to_cook_normalized` | `lean/MCore/Real/CookNormalizedOfficialBinding.lean`:40 | nao_alcancado |
| `MCore.Real.OpenMathCore.addPotential_apply` | `lean/MCore/Real/OpenMathCore/Algebra.lean`:23 | nao_alcancado |
| `MCore.Real.OpenMathCore.addPotential_assoc` | `lean/MCore/Real/OpenMathCore/Algebra.lean`:29 | nao_alcancado |
| `MCore.Real.OpenMathCore.arithmeticMass_append` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:53 | fechado |
| `MCore.Real.OpenMathCore.bitLength_append` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:34 | fechado |
| `MCore.Real.OpenMathCore.bitLength_nil` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:32 | fechado |
| `MCore.Real.OpenMathCore.bitNat_le_one` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:38 | fechado |
| `MCore.Real.OpenMathCore.bitWeight_append` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:25 | fechado |
| `MCore.Real.OpenMathCore.bitWeight_cons` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:22 | fechado |
| `MCore.Real.OpenMathCore.bitWeight_le_length` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:41 | fechado |
| `MCore.Real.OpenMathCore.bitWeight_nil` | `lean/MCore/Real/OpenMathCore/Arithmetic.lean`:20 | fechado |
| `MCore.Real.OpenMathCore.candidate_encode_injective` | `lean/MCore/Real/OpenMathCore/ReductionBarrier.lean`:17 | nao_alcancado |
| `MCore.Real.OpenMathCore.canonical_encode_injective` | `lean/MCore/Real/OpenMathCore/Foundation.lean`:30 | fechado |
| `MCore.Real.OpenMathCore.codec_encode_injective` | `lean/MCore/Real/OpenMathCore/Functoriality.lean`:27 | fechado |
| `MCore.Real.OpenMathCore.extensional_fixed_point` | `lean/MCore/Real/OpenMathCore/KleeneExtensionalProducer.lean`:31 | fechado |
| `MCore.Real.OpenMathCore.kleene_shortcut_is_not_stronger` | `lean/MCore/Real/OpenMathCore/ReductionBarrier.lean`:34 | nao_alcancado |
| `MCore.Real.OpenMathCore.mismatch_exact` | `lean/MCore/Real/OpenMathCore/Semantics.lean`:17 | nao_alcancado |
| `MCore.Real.OpenMathCore.mismatch_iff_not_declared_match` | `lean/MCore/Real/OpenMathCore/Semantics.lean`:24 | nao_alcancado |
| `MCore.Real.OpenMathCore.observableNorm_nonneg` | `lean/MCore/Real/OpenMathCore/NumericClasses.lean`:37 | nao_alcancado |
| `MCore.Real.OpenMathCore.resourceLaw_space_poly` | `lean/MCore/Real/OpenMathCore/Asymptotic.lean`:22 | nao_alcancado |
| `MCore.Real.OpenMathCore.resourceLaw_time_poly` | `lean/MCore/Real/OpenMathCore/Asymptotic.lean`:16 | nao_alcancado |
| `MCore.Real.OpenMathCore.scalePotential_apply` | `lean/MCore/Real/OpenMathCore/Algebra.lean`:26 | nao_alcancado |
| `MCore.Real.OpenMathCore.scale_addPotential` | `lean/MCore/Real/OpenMathCore/Algebra.lean`:35 | nao_alcancado |
| `MCore.Real.OpenMathCore.scanner_transition_preserves_phase_set` | `lean/MCore/Real/OpenMathCore/Invariants.lean`:18 | nao_alcancado |
| `MCore.Real.OpenMathCore.separation_stable_under_auxiliary_change` | `lean/MCore/Real/OpenMathCore/Stability.lean`:16 | nao_alcancado |
| `MCore.Real.OpenMathCore.terminal_independent_of_auxiliary_bundle` | `lean/MCore/Real/OpenMathCore/Stability.lean`:24 | nao_alcancado |
| `MCore.Real.OpenMathCore.totalCandidateSeparationLaw_closes_core` | `lean/MCore/Real/OpenMathCore/Behavior.lean`:30 | nao_alcancado |
| `MCore.Real.OpenMathCore.totalSemanticSeparation_iff_core` | `lean/MCore/Real/OpenMathCore/Semantics.lean`:36 | nao_alcancado |
| `MCore.Real.OpenMathCore.uniform_extensional_compiler_gives_mismatch` | `lean/MCore/Real/OpenMathCore/KleeneExtensionalProducer.lean`:83 | fechado |
| `MCore.Real.OpenMathCore.witnessOfExtensionalCompiler_flip` | `lean/MCore/Real/OpenMathCore/KleeneExtensionalProducer.lean`:54 | fechado |
| `MCore.Real.OpenMathCore.witnessOfExtensionalCompiler_valid` | `lean/MCore/Real/OpenMathCore/KleeneExtensionalProducer.lean`:46 | fechado |
| `MCore.Real.OpenMathUniversalSeparationLaw.universalLaw_iff_t5F` | `lean/MCore/Real/OpenMathUniversalSeparationLaw.lean`:188 | nao_alcancado |
| `MCore.Real.P02CandidateCodingFrontier.candidateCodingInterface_impossible` | `lean/MCore/Real/P02CandidateCodingCardinalityFirewall.lean`:43 | fechado |
| `MCore.Real.P02CandidateCodingFrontier.codingFirewallCandidate_injective` | `lean/MCore/Real/P02CandidateCodingCardinalityFirewall.lean`:31 | fechado |
| `MCore.Real.P02CandidateCodingFrontier.codingFirewallTimeBound_poly` | `lean/MCore/Real/P02CandidateCodingCardinalityFirewall.lean`:16 | fechado |
| `MCore.Real.P02FiniteClockCandidateModel.finiteClockUniversalFailure_implies_UniversalFailure` | `lean/MCore/Real/P02FiniteClockCandidateModel.lean`:47 | fechado |
| `MCore.Real.P02FiniteClockCandidateModel.finiteClockUniversalFailure_implies_not_in_p` | `lean/MCore/Real/P02FiniteClockCandidateModel.lean`:62 | fechado |
| `MCore.Real.P02FiniteClockCandidateModel.ofCandidateClock_toPoly` | `lean/MCore/Real/P02FiniteClockCandidateModel.lean`:37 | fechado |
| `MCore.Real.P02FiniteClockCountability.describe_injective` | `lean/MCore/Real/P02FiniteClockCountability.lean`:71 | nao_alcancado |
| `MCore.Real.P02FiniteClockCountability.finite_clock_candidate_countable` | `lean/MCore/Real/P02FiniteClockCountability.lean`:83 | nao_alcancado |
| `MCore.Real.P02FiniteClockCountability.realize_describe` | `lean/MCore/Real/P02FiniteClockCountability.lean`:62 | nao_alcancado |
