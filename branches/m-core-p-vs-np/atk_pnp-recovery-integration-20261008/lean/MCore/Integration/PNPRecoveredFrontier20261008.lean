import MCore.Real.P01RawTotalizationProducer
import MCore.Real.CanonicalSATBoundary

/-!
# P ≠ NP recovery integration — 2026-10-08

Composition only. This file modifies no existing proof; it imports already
frozen material and composes it.

## Recovered material (kernel-checked, not re-proved here)

* `P01RawTotalizationProducer.p01ConstructionGap_closed : P01ConstructionGap`
  - parent of this branch: `0dd09383932446ba67e673f69cd8740f85a80b87`
    (ref `frozen/p01-t5-poly-halting-green-0dd09383`);
  - CI kernel evidence for the producer: run `36897479263`
    (`p01-verifier-phase-mincut-clean.yml`, success) at
    `15b6c36043721e827930c98babbaa3e0e9f50456`, an ancestor of `0dd0938` in
    which the producer file and its imports are byte-identical. That workflow
    runs `lake build MCore.Real.P01RawTotalizationProducer`. Run `37354059689`
    at `0dd0938` certified a different workflow (preserving reader) and does
    not build the producer.
  - unconditional, axioms `[propext, Classical.choice, Quot.sound]`.
  - Content: a concrete finite-state polynomial-time NTM that decides the
    canonical CNF-SAT bit language. This is the SAT ∈ NP side only.

## Remaining obligation (OPEN_MATH)

`G21Pointwise` below has the same body as
`MCore.Real.P02G21G22Attack.G21Pointwise`
(`origin/atk/g21-final-integration-clean-20260930`). A search of all 684
branches (full history), 53 pull-request refs and five further repositories
found no unconditional inhabitant of it, nor of `PneqNP`, `P02Target`,
`SATFailGap`, `UniversalFailure SATTarget`, or `¬ InP SATTarget`. Every
theorem found that concludes `PneqNP` takes a hypothesis, and none of those
hypothesis types has an unconditional inhabitant.

`G21Pointwise` is definitionally `UniversalFailure SATTarget`, and is
equivalent (using classical logic) to `¬ InP SATTarget`: "SAT is not in P".
It cannot be removed by renaming, reclassifying, or routing it through an
adapter.
-/

namespace MCore
namespace Integration
namespace PNPRecoveredFrontier20261008

open MCore.Real
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps

/-- The fixed canonical SAT bit-language. -/
abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- Recovered P01: SAT ∈ NP in the hardened machine model. -/
theorem sat_in_np_recovered : InNP SATTarget :=
  P01FinalCertificate.construction_closes_p01
    P01RawTotalizationProducer.p01ConstructionGap_closed

/-- The single remaining obligation. The body is identical to
`P02G21G22Attack.G21Pointwise`. -/
def G21Pointwise : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ candidate.CorrectAt SATTarget x

/-- G21 is definitionally the universal fail proof for SAT. -/
theorem g21_iff_universal_failure :
    G21Pointwise ↔ UniversalFailure SATTarget :=
  Iff.rfl

/-- G21 is equivalent to "SAT is not in P" (classical direction via
`not_in_p_implies_universal_failure`). -/
theorem g21_iff_sat_not_in_p :
    G21Pointwise ↔ ¬ InP SATTarget :=
  universal_failure_iff_not_in_p

/-- G21 is exactly the `SATFailGap` / `FailureGenerator` producer. -/
theorem g21_iff_sat_fail_gap :
    G21Pointwise ↔ SATFailGap circuitBitEncoding :=
  failure_generator_iff_universal_failure.symm

/-- Integrated endpoint with P01 discharged: exactly one hypothesis remains. -/
theorem pneqnp_of_g21 (hG21 : G21Pointwise) : PneqNP :=
  target_failure_implies_p_ne_np sat_in_np_recovered hG21

/-- Same endpoint, stated with the remaining hypothesis in its plain form. -/
theorem pneqnp_of_sat_not_in_p (hNotP : ¬ InP SATTarget) : PneqNP :=
  pneqnp_of_g21 (g21_iff_sat_not_in_p.mpr hNotP)

/-- Integration status, in one statement: P01 is closed, and the only path
to `PneqNP` assembled here goes through `¬ InP SATTarget`. -/
theorem integration_status :
    InNP SATTarget ∧
      (G21Pointwise ↔ ¬ InP SATTarget) ∧
      (G21Pointwise → PneqNP) :=
  ⟨sat_in_np_recovered, g21_iff_sat_not_in_p, pneqnp_of_g21⟩

#print axioms MCore.Integration.PNPRecoveredFrontier20261008.sat_in_np_recovered
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.g21_iff_universal_failure
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.g21_iff_sat_not_in_p
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.g21_iff_sat_fail_gap
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.pneqnp_of_g21
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.pneqnp_of_sat_not_in_p
#print axioms MCore.Integration.PNPRecoveredFrontier20261008.integration_status

end PNPRecoveredFrontier20261008
end Integration
end MCore
