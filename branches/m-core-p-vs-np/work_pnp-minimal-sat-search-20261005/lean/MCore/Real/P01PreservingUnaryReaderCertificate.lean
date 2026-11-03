import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01InputNodePreservingPlan
import MCore.Real.P01EvalCursorMachine

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01EncodedStackEvaluator
open P01InputNodePreservingPlan
open P01PreservingUnaryWitnessMachine

/-!
# Exact terminal contract for the remaining P01 input-node reader

This contract is intentionally stronger than merely returning the right bit.
It requires one fixed finite-control TM, polynomial halting, exact witness
preservation, and a Boolean result encoded in the terminal state.

No field contains the answer as an unconstrained function and no field permits
the variable index to be stored in an unbounded control-state parameter.
-/

structure PreservingUnaryReaderCertificate where
  machine : TM PreservingReadState (Option Bool)
  machine_eq : machine = preservingUnaryReadMachine
  accepting : PreservingReadState → Bool
  accepting_eq : accepting = preservingReadAccepting
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ (witness : BitString) (i : Nat),
      i < witness.length →
      machine.HaltsWithin (timeBound (witness.length + (encodeNat i).length))
        { state := machine.initial
          tape := witnessReadTape witness i }

  correct :
    ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
      accepting
        (machine.run
          (timeBound (witness.length + (encodeNat i).length))
          { state := machine.initial
            tape := witnessReadTape witness i }).state =
        witness.getD i false

  preservesWitness :
    ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
      ∃ left right : List (Option Bool),
        (machine.run
          (timeBound (witness.length + (encodeNat i).length))
          { state := machine.initial
            tape := witnessReadTape witness i }).tape =
          { left := left ++ witness.map some
            head := none
            right := right }

def PreservingUnaryReaderGap : Prop :=
  Nonempty PreservingUnaryReaderCertificate

/-- Zero index is already completely solved by the concrete machine. -/
def zeroTimeBound : TimeBound := fun _ => 5

theorem zeroTimeBound_poly :
    PolynomialTimeBound zeroTimeBound := by
  exact ⟨5, 0, by intro n; simp [zeroTimeBound]⟩

theorem zero_case_halts
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.HaltsWithin 5
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) 0 } := by
  unfold TM.HaltsWithin
  rw [preservingRead_zero_run_five]
  cases b <;> rfl

/-- Semantic input-node correctness follows immediately once the physical
reader returns the same witness bit as the Assignment.  This is the exact
bridge needed by the global evalStep refinement. -/
theorem input_semantic_from_reader_bit
    (sigma : Assignment)
    (witness : BitString)
    (i : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (hbit : sigma i = witness.getD i false) :
    evalStep sigma
      (needExpr
        (false :: false :: false :: (encodeNat i ++ rest))
        frames) =
      some (haveValue (witness.getD i false) rest frames) := by
  rw [evalStep_input_encoded]
  rw [hbit]

/-- The physical reader gap is a genuine implementation obligation: the
already-proved zero-index case alone does not inhabit the universal contract. -/
theorem zero_case_is_component
    (b : Bool) (tail : BitString) :
    preservingReadAccepting
      (preservingUnaryReadMachine.run 5
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape (b :: tail) 0 }).state =
      (b :: tail).getD 0 false := by
  rw [preservingRead_zero_correct]
  simp [List.getD_cons_zero]

#print axioms MCore.Real.P01PreservingUnaryReaderCertificate.zero_case_halts
#print axioms MCore.Real.P01PreservingUnaryReaderCertificate.input_semantic_from_reader_bit
#print axioms MCore.Real.P01PreservingUnaryReaderCertificate.zero_case_is_component

end P01PreservingUnaryReaderCertificate
end Real
end MCore
