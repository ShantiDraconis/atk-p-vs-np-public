import MCore.Real.P01FullVerifierStackPrimitiveMachine
import MCore.Real.P01FullVerifierEvalLocal

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalOps

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2
open P01FullVerifierStackPrimitiveMachine
open P01FullVerifierStackSemantics

/-- Push a constant bit using the real one-step stack primitive. -/
theorem const_run_real
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) (b : Bool) :
    PhysicalStackRepV2
      (stackPrimitiveMachine.run 1
        (pushConfig b (physicalStackV2Tape witness source stack padding))).tape
      witness source (b :: stack) := by
  exact push_run_one_rep witness source stack padding b

/-- Negation is pop followed by push of the flipped bit. The two pop-result
states carry exactly one Boolean of finite control, so this stays fixed-state. -/
def negResultBit (q : StackState) : Option Bool :=
  if q = haltPopFalse then some true
  else if q = haltPopTrue then some false
  else none

theorem neg_pop_exposes_false
    (witness source : BitString) (stack : List Bool) (padding : Nat) :
    let final := stackPrimitiveMachine.run 2
      (popConfig (physicalStackV2Tape witness source (false :: stack) padding))
    negResultBit final.state = some true /\
      PhysicalStackRepV2 final.tape witness source stack := by
  have h := pop_run_two_false witness source stack padding
  rcases h with ⟨hstate, hrep⟩
  constructor
  · simp [negResultBit, hstate, haltPopFalse, haltPopTrue]
  · exact hrep

theorem neg_pop_exposes_true
    (witness source : BitString) (stack : List Bool) (padding : Nat) :
    let final := stackPrimitiveMachine.run 2
      (popConfig (physicalStackV2Tape witness source (true :: stack) padding))
    negResultBit final.state = some false /\
      PhysicalStackRepV2 final.tape witness source stack := by
  have h := pop_run_two_true witness source stack padding
  rcases h with ⟨hstate, hrep⟩
  constructor
  · simp [negResultBit, hstate, haltPopFalse, haltPopTrue]
  · exact hrep

/-- Semantic target for physical AND after consuming r then l. -/
theorem and_semantic_target
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .and =
      some (Bool.and l r :: stack) := by
  exact P01FullVerifierEvalLocal.evalAnd_local_semantics sigma l r stack

/-- Semantic target for physical OR after consuming r then l. -/
theorem or_semantic_target
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .or =
      some (Bool.or l r :: stack) := by
  exact P01FullVerifierEvalLocal.evalOr_local_semantics sigma l r stack

/-- The primitive pop machine exactly exposes the first operand for a binary gate. -/
theorem first_operand_pop
    (witness source : BitString)
    (r : Bool) (rest : List Bool) (padding : Nat) :
    let final := stackPrimitiveMachine.run 2
      (popConfig (physicalStackV2Tape witness source (r :: rest) padding))
    (if r then final.state = haltPopTrue else final.state = haltPopFalse) /\
      PhysicalStackRepV2 final.tape witness source rest := by
  cases r
  · simpa using pop_run_two_false witness source rest padding
  · simpa using pop_run_two_true witness source rest padding

#print axioms MCore.Real.P01FullVerifierPhysicalOps.const_run_real
#print axioms MCore.Real.P01FullVerifierPhysicalOps.neg_pop_exposes_false
#print axioms MCore.Real.P01FullVerifierPhysicalOps.neg_pop_exposes_true
#print axioms MCore.Real.P01FullVerifierPhysicalOps.and_semantic_target
#print axioms MCore.Real.P01FullVerifierPhysicalOps.or_semantic_target
#print axioms MCore.Real.P01FullVerifierPhysicalOps.first_operand_pop

end P01FullVerifierPhysicalOps
end Real
end MCore
