import MCore.Real.P01FullVerifierPhysicalRefinementV2
import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01PhysicalVerifierUniformCosts
import MCore.Real.P01PhysicalRealizationAssembly
import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore
namespace Real
namespace PhysicalMachineCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01FullVerifierStackSemantics
open P01FullVerifierPhysicalControl
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalRefinementV2
open P01FullVerifierInputShuttleV2
open P01FullVerifierPhysicalMoves
open P01PhysicalVerifierUniformCosts
open P01PhysicalRealizationAssembly

/-- Exact global representation invariant used to compose the local physical
instruction lemmas.  Source and witness preservation are structural: both are
encoded literally in physicalStackV2Tape. -/
structure PhysicalInvariant
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (tape : Tape (Option Bool)) : Prop where
  tape_eq :
    tape = physicalStackV2Tape witness source stack padding

theorem invariant_refl
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat) :
    PhysicalInvariant witness source stack padding
      (physicalStackV2Tape witness source stack padding) := by
  exact ⟨rfl⟩

/-- Constant evaluator step preserves the global physical representation. -/
theorem const_refines
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (b : Bool) :
    PhysicalInvariant witness source (b :: stack) (padding - 1)
      (pushStep b (physicalStackV2Tape witness source stack padding)) := by
  refine ⟨?_⟩
  exact physical_const_sequence_exact witness source stack padding b

/-- Negation evaluator step preserves the global physical representation. -/
theorem neg_refines
    (witness source : BitString)
    (v : Bool)
    (stack : List Bool)
    (padding : Nat) :
    PhysicalInvariant witness source ((!v) :: stack) padding
      (pushStep (!v)
        (popErase
          (popEnter
            (physicalStackV2Tape witness source (v :: stack) padding)))) := by
  refine ⟨?_⟩
  exact physical_neg_sequence_exact witness source v stack padding

/-- Conjunction evaluator step preserves the global physical representation. -/
theorem and_refines
    (witness source : BitString)
    (l r : Bool)
    (stack : List Bool)
    (padding : Nat) :
    PhysicalInvariant witness source (Bool.and l r :: stack) (padding + 1)
      (pushStep (Bool.and l r)
        (popErase
          (popEnter
            (popErase
              (popEnter
                (physicalStackV2Tape witness source
                  (r :: l :: stack) padding)))))) := by
  refine ⟨?_⟩
  exact physical_and_sequence_exact witness source l r stack padding

/-- Disjunction evaluator step preserves the global physical representation. -/
theorem or_refines
    (witness source : BitString)
    (l r : Bool)
    (stack : List Bool)
    (padding : Nat) :
    PhysicalInvariant witness source (Bool.or l r :: stack) (padding + 1)
      (pushStep (Bool.or l r)
        (popErase
          (popEnter
            (popErase
              (popEnter
                (physicalStackV2Tape witness source
                  (r :: l :: stack) padding)))))) := by
  refine ⟨?_⟩
  exact physical_or_sequence_exact witness source l r stack padding

/-- The input branch is reduced to the already-certified physical witness
lookup.  It deliberately does not claim the global dispatcher run yet. -/
theorem input_head_refines
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    (execMoves (none : Option Bool)
      (moveLeftSeq (stackWitnessOffset stack source i))
      (physicalStackV2Tape witness source stack padding)).head =
      some witness[i] := by
  exact stackV2_witness_head_correct witness source stack padding i hi

/-- Exact logical one-instruction relation.  This is the semantic side of the
remaining machine-run refinement theorem. -/
def LogicalExecStep
    (sigma : Assignment)
    (instr : EvalInstr)
    (stack stack' : List Bool) : Prop :=
  execInstr sigma stack instr = some stack'

/-- Exact logical whole-program relation. -/
def LogicalProgramRun
    (sigma : Assignment)
    (program : List EvalInstr)
    (stack stack' : List Bool) : Prop :=
  runProgram sigma program stack = some stack'

/-- Uniform physical evaluator envelope already proved by the existing cost
layer. -/
def physicalProgramCostBound (n : Nat) : Nat :=
  8 * (n + 1) ^ 2

theorem evalProgram_cost_le_physicalProgramCostBound
    (phi : CircuitK1.Circuit) :
    (evalProgram phi).length *
        physicalInstructionCostBound (encodeCircuit phi).length
      ≤ physicalProgramCostBound (encodeCircuit phi).length := by
  simpa [physicalProgramCostBound] using
    (evalProgram_physical_cost_quadratic phi)

/-- Contract for the one fixed finite-control physical verifier.  This is
strictly weaker than PhysicalMachineCore because it isolates only the remaining
global run/refinement obligations and does not assume P01 or SAT-in-NP. -/
structure FixedPhysicalVerifierRefinement where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
      machine.HaltsWithin
        (timeBound (encodeCircuit phi).length)
        { state := machine.initial,
          tape := P01FullVerifierMachine.verifierInputTape
            (witnessBits w) (encodeCircuit phi) }
  refines :
    ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
      accepting
        (machine.run
          (timeBound (encodeCircuit phi).length)
          { state := machine.initial,
            tape := P01FullVerifierMachine.verifierInputTape
              (witnessBits w) (encodeCircuit phi) }).state = true ↔
        verifyWitness phi w = true

def FixedPhysicalVerifierRefinement.toPhysicalMachineCore
    (R : FixedPhysicalVerifierRefinement) :
    P01PhysicalRealizationAssembly.PhysicalMachineCore where
  stateCount := R.stateCount
  machine := R.machine
  blank_none := R.blank_none
  accepting := R.accepting
  timeBound := R.timeBound
  time_poly := R.time_poly
  halts := R.halts
  correct := R.refines

def FixedPhysicalVerifierRefinement.toRealization
    (R : FixedPhysicalVerifierRefinement) :
    P01FullVerifierPhysical.PhysicalVerifierRealization :=
  R.toPhysicalMachineCore.toRealization

theorem fixed_refinement_closes_physicalVerifierGap
    (R : FixedPhysicalVerifierRefinement) :
    P01FullVerifierPhysical.PhysicalVerifierGap := by
  exact ⟨R.toRealization⟩

#print axioms MCore.Real.PhysicalMachineCore.const_refines
#print axioms MCore.Real.PhysicalMachineCore.neg_refines
#print axioms MCore.Real.PhysicalMachineCore.and_refines
#print axioms MCore.Real.PhysicalMachineCore.or_refines
#print axioms MCore.Real.PhysicalMachineCore.input_head_refines
#print axioms MCore.Real.PhysicalMachineCore.evalProgram_cost_le_physicalProgramCostBound
#print axioms MCore.Real.PhysicalMachineCore.fixed_refinement_closes_physicalVerifierGap

end PhysicalMachineCore
end Real
end MCore
