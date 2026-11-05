import P02.LANE4.AUX.R1_R3_REAL
import P02.LANE4.AUX.R4_FINAL
import P02.LANE4.AUX.R5_PAIR_INJECTIVE
import MCore.Real.P02BehavioralAlignment

namespace P02
namespace LANE4

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding
open MCore.Real.P02ComplementRunRealization
open MCore.Real.P02BehavioralAlignment

/-- All structural/information-preservation obligations for LANE4, kept
strictly separate from the behavioral OPEN_MATH frontier. -/
structure StructuralClosure where
  r1_inputTape_injective :
    Function.Injective inputTape
  r3_ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit
  r4_boundedExecCircuit_same_params_injective :
    ∀ (M : PolyNTMCandidate) (t : Nat),
      Function.Injective (fun x => boundedExecCircuit_NTM M x t)
  r5_tableau_pair_injective :
    ∀ (M : PolyNTMCandidate)
      {x y : BitString}
      {tx ty : Nat},
      boundedExecTableauCNF_NTM M x tx =
        boundedExecTableauCNF_NTM M y ty →
      tx = ty ∧ x = y
  r5_circuit_pair_injective :
    ∀ (M : PolyNTMCandidate)
      {x y : BitString}
      {tx ty : Nat},
      boundedExecCircuit_NTM M x tx =
        boundedExecCircuit_NTM M y ty →
      tx = ty ∧ x = y
  r5_complement_reduce_injective :
    ∀ (M : PolyDTMCandidate)
      (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M),
      Function.Injective (complementSemanticReduction M hTotal).reduce

/-- Concrete structural inhabitant.  This is AUX-only: it does not construct
a behavioral diagonal witness and therefore does not close T10. -/
def structuralClosure : StructuralClosure where
  r1_inputTape_injective :=
    AUX.R1_R3_REAL.inputTape_injective
  r3_ntmCNFCircuit_injective :=
    AUX.R1_R3_REAL.ntmCNFCircuit_injective
  r4_boundedExecCircuit_same_params_injective :=
    AUX.R4_FINAL.boundedExecCircuit_same_params_injective
  r5_tableau_pair_injective :=
    AUX.R5_PAIR_INJECTIVE.boundedExecTableau_pair_injective
  r5_circuit_pair_injective :=
    AUX.R5_PAIR_INJECTIVE.boundedExecCircuit_pair_injective
  r5_complement_reduce_injective :=
    AUX.R5_PAIR_INJECTIVE.reduce_M_injective_final

/-- Exact remaining semantic frontier. -/
abbrev T10_OPEN_MATH : Prop :=
  TotalBehavioralAlignmentProducer

/-- Structural closure plus the missing semantic producer is sufficient for
the exact-diagonal producer.  The structural argument is deliberately not
used as a substitute for the behavioral producer. -/
theorem t10_open_math_to_exact
    (_S : StructuralClosure)
    (B : T10_OPEN_MATH) :
    P02ExactDiagonalFrontier.TotalExactDiagonalProducer :=
  total_behavioral_alignment_to_exact B

/-- The pair-injective data can be projected directly from the aggregate. -/
theorem structural_tableau_pair_recovery
    (M : PolyNTMCandidate)
    {x y : BitString}
    {tx ty : Nat}
    (h :
      boundedExecTableauCNF_NTM M x tx =
        boundedExecTableauCNF_NTM M y ty) :
    tx = ty ∧ x = y :=
  structuralClosure.r5_tableau_pair_injective M h

/-- The aggregate never supplies behavioral preservation.  T10 remains an
explicit independent input to the terminal composition theorem. -/
theorem structural_plus_behavioral_to_exact
    (S : StructuralClosure)
    (B : T10_OPEN_MATH) :
    P02ExactDiagonalFrontier.TotalExactDiagonalProducer :=
  t10_open_math_to_exact S B

#print axioms P02.LANE4.structuralClosure
#print axioms P02.LANE4.structural_tableau_pair_recovery
#print axioms P02.LANE4.t10_open_math_to_exact
#print axioms P02.LANE4.structural_plus_behavioral_to_exact

end LANE4
end P02
