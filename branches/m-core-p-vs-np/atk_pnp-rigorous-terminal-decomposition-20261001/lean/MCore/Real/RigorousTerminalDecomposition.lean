import MCore.Real.EncodedFinalProof

namespace MCore
namespace Real
namespace RigorousTerminalDecomposition

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open P01FinalCertificate
open EncodedFinalProof

/-- Exact lower-bound target in the hardened canonical-input model. -/
abbrev EncodedP02Target : Prop :=
  EncodedUniversalSATFailure

/-- Non-membership in encoded P is equivalent to a concrete failing input for
every deterministic polynomial-time candidate in the same fixed-input model. -/
theorem encoded_sat_not_in_p_implies_universal_failure
    (hNotP : EncodedSATNotInP) :
    EncodedUniversalSATFailure := by
  intro candidate
  apply Classical.byContradiction
  intro hNoFailure
  apply hNotP
  refine ⟨{
    candidate := candidate
    decides := ?_
  }⟩
  intro phi
  apply Classical.byContradiction
  intro hBad
  exact hNoFailure ⟨phi, hBad⟩

theorem encoded_p02_target_iff_sat_not_in_p :
    EncodedP02Target ↔ EncodedSATNotInP := by
  constructor
  · exact encoded_failure_implies_sat_not_in_p
  · exact encoded_sat_not_in_p_implies_universal_failure

/-- The canonical input is not supplied by a language-dependent encoder:
CorrectAt always starts from the fixed circuit bit encoding. -/
theorem correctAt_uses_canonical_input
    (candidate : EncodedPolyDTMCandidate)
    (language : Circuit → Prop)
    (phi : Circuit) :
    candidate.CorrectAt language phi ↔
      let cfg :=
        initialTMConfig candidate.machine (encodeCircuit phi)
      candidate.machine.HaltsWithin
          (candidate.timeBound (EncodedCircuitSize phi)) cfg ∧
        (candidate.accepting
            (candidate.machine.run
              (candidate.timeBound (EncodedCircuitSize phi)) cfg).state = true
          ↔ language phi) := by
  rfl

/-- Exact two-producer SAT route in the hardened model.

P01 is the constructive NP witness. P02 is the genuine universal deterministic
failure producer. Neither field is a renamed copy of the other.
-/
structure RigorousPNPFinalPair : Prop where
  p01 : P01ConstructionGap
  p02 : EncodedP02Target

def RIGOROUS_SAT_RESIDUAL : Prop :=
  P01ConstructionGap ∧ EncodedP02Target

theorem rigorous_pair_to_root
    (C : RigorousPNPFinalPair) :
    RIGOROUS_FINAL_ROOT :=
  encoded_sat_boundary_implies_separation
    (encodedSATInNP_of_P01Gap C.p01)
    ⟨C.p02⟩

theorem rigorous_residual_to_root
    (h : RIGOROUS_SAT_RESIDUAL) :
    RIGOROUS_FINAL_ROOT :=
  rigorous_pair_to_root
    { p01 := h.1
      p02 := h.2 }

/-- Once a real P01 inhabitant is fixed, the only remaining producer on this
SAT route is the hardened P02 lower bound. -/
theorem root_of_fixed_p01
    (hP01 : P01ConstructionGap)
    (hP02 : EncodedP02Target) :
    RIGOROUS_FINAL_ROOT :=
  rigorous_residual_to_root ⟨hP01, hP02⟩

/-- A P02 target can be packaged into the external lower-bound certificate
without changing its mathematical content. -/
def p02_to_lower_bound_certificate
    (hP02 : EncodedP02Target) :
    EncodedSATLowerBoundCertificate :=
  ⟨hP02⟩

#print axioms MCore.Real.RigorousTerminalDecomposition.encoded_sat_not_in_p_implies_universal_failure
#print axioms MCore.Real.RigorousTerminalDecomposition.encoded_p02_target_iff_sat_not_in_p
#print axioms MCore.Real.RigorousTerminalDecomposition.correctAt_uses_canonical_input
#print axioms MCore.Real.RigorousTerminalDecomposition.rigorous_residual_to_root
#print axioms MCore.Real.RigorousTerminalDecomposition.root_of_fixed_p01

end RigorousTerminalDecomposition
end Real
end MCore
