import MCore.Real.CanonicalSATParserAttack
import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace P01ComponentFailProof

open CanonicalFinalProof
open CanonicalSATNTMAttack

/-!
P01 component fail-proof.

The three component certificate structures introduced in
CanonicalSATNTMAttack carry only a machine and a polynomial time-bound field;
none of them states what the machine must parse, guess, or verify.  This file
machine-checks that all three are therefore trivially inhabitable.

This is a specification RED, not a statement about SAT or P versus NP.
-/

private def trivialTM : TM (Fin 1) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol => (q, symbol, .stay)
    halting := fun _ => true }

private def trivialNTM : NTM (Fin 1) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun _ _ => []
    accepting := fun _ => true
    rejecting := fun _ => false }

private theorem zero_bound_poly :
    PolynomialTimeBound (fun _ => 0) := by
  refine ⟨0, 0, ?_⟩
  intro n
  simp

theorem parser_component_is_trivially_inhabited :
    Nonempty ParserMachineCertificate := by
  exact ⟨
    { stateCount := 0
      machine := trivialTM
      timeBound := fun _ => 0
      time_poly := zero_bound_poly }⟩

theorem witness_guess_component_is_trivially_inhabited :
    Nonempty WitnessGuessMachineCertificate := by
  exact ⟨
    { stateCount := 0
      machine := trivialNTM
      timeBound := fun _ => 0
      time_poly := zero_bound_poly }⟩

theorem verifier_component_is_trivially_inhabited :
    Nonempty VerifierMachineCertificate := by
  exact ⟨
    { stateCount := 0
      machine := trivialTM
      timeBound := fun _ => 0
      time_poly := zero_bound_poly }⟩

theorem all_legacy_components_are_trivially_inhabited :
    Nonempty ParserMachineCertificate ∧
    Nonempty WitnessGuessMachineCertificate ∧
    Nonempty VerifierMachineCertificate := by
  exact ⟨
    parser_component_is_trivially_inhabited,
    witness_guess_component_is_trivially_inhabited,
    verifier_component_is_trivially_inhabited
  ⟩

/-- The parser boundary that is semantically meaningful in the current tree:
it requires halting and exact agreement with decodeCircuit on every bitstring. -/
abbrev HardenedParserGap : Prop :=
  CanonicalSATParserAttack.CanonicalRecursiveParserOperationalGap

/-- P01 itself remains the actual canonical SAT-in-NP machine realization,
not the existence of the three legacy component records. -/
abbrev P01OperationalTarget : Prop :=
  CanonicalSATNTMAttack.CanonicalSATMachineClosure

#print axioms MCore.Real.P01ComponentFailProof.parser_component_is_trivially_inhabited
#print axioms MCore.Real.P01ComponentFailProof.witness_guess_component_is_trivially_inhabited
#print axioms MCore.Real.P01ComponentFailProof.verifier_component_is_trivially_inhabited
#print axioms MCore.Real.P01ComponentFailProof.all_legacy_components_are_trivially_inhabited

end P01ComponentFailProof
end Real
end MCore
