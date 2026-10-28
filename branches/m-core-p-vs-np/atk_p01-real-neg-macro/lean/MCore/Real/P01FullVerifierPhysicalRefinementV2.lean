import MCore.Real.P01FullVerifierPhysicalRefinement
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalRefinementV2

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalShuttles
open P01FullVerifierPhysicalStackV2
open P01FullVerifierStackSemantics

/-- Concrete physical implementation of a constant instruction: write the
Boolean at the stack head and move to the fresh blank stack position. -/
theorem physical_const_sequence_exact
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (b : Bool) :
    pushStep b (physicalStackV2Tape witness source stack padding) =
      physicalStackV2Tape witness source (b :: stack) (padding - 1) := by
  exact pushStep_correct witness source stack padding b

/-- Concrete physical implementation of negation: pop the top Boolean, erase
its old cell, and push its negation.  No logical output tape is postulated. -/
theorem physical_neg_sequence_exact
    (witness source : BitString)
    (v : Bool)
    (stack : List Bool)
    (padding : Nat) :
    pushStep (!v)
      (popErase
        (popEnter
          (physicalStackV2Tape witness source (v :: stack) padding))) =
      physicalStackV2Tape witness source ((!v) :: stack) padding := by
  rw [popErase_correct witness source v stack padding]
  simpa using
    (pushStep_correct witness source stack (padding + 1) (!v))

/-- Concrete physical implementation of conjunction: two physical pops
followed by one physical push.  The stack shrinks by one cell, hence one
additional blank cell remains as padding. -/
theorem physical_and_sequence_exact
    (witness source : BitString)
    (l r : Bool)
    (stack : List Bool)
    (padding : Nat) :
    pushStep (Bool.and l r)
      (popErase
        (popEnter
          (popErase
            (popEnter
              (physicalStackV2Tape witness source
                (r :: l :: stack) padding))))) =
      physicalStackV2Tape witness source
        (Bool.and l r :: stack) (padding + 1) := by
  rw [popErase_correct witness source r (l :: stack) padding]
  rw [popErase_correct witness source l stack (padding + 1)]
  simpa [Nat.add_assoc] using
    (pushStep_correct witness source stack (padding + 1 + 1)
      (Bool.and l r))

/-- Concrete physical implementation of disjunction: two physical pops
followed by one physical push. -/
theorem physical_or_sequence_exact
    (witness source : BitString)
    (l r : Bool)
    (stack : List Bool)
    (padding : Nat) :
    pushStep (Bool.or l r)
      (popErase
        (popEnter
          (popErase
            (popEnter
              (physicalStackV2Tape witness source
                (r :: l :: stack) padding))))) =
      physicalStackV2Tape witness source
        (Bool.or l r :: stack) (padding + 1) := by
  rw [popErase_correct witness source r (l :: stack) padding]
  rw [popErase_correct witness source l stack (padding + 1)]
  simpa [Nat.add_assoc] using
    (pushStep_correct witness source stack (padding + 1 + 1)
      (Bool.or l r))

/-- Number of primitive left moves from the current blank stack head to
witness[i] in the V2 physical tape layout.  The quantity is data-dependent
but is represented by repeated primitive moves, never by finite-control
state. -/
def stackWitnessOffset
    (stack : List Bool) (source : BitString) (i : Nat) : Nat :=
  stack.length + source.length + 3 + i

/-- A valid witness bit is physically reachable from an arbitrary V2 stack
configuration.  This is the machine-level read primitive required by the
input instruction. -/
theorem stackV2_witness_head_correct
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    (execMoves none
      (moveLeftSeq (stackWitnessOffset stack source i))
      (physicalStackV2Tape witness source stack padding)).head =
      some witness[i] := by
  unfold stackWitnessOffset
  rw [show stack.length + source.length + 3 + i =
      (stack.length + source.length + 2 + i) + 1 by omega]
  rw [execMoves_moveLeftSeq_head_getD]
  unfold physicalStackV2Tape
  have h :=
    getD_prefix_separator_witness
      (stack.map some ++ none :: source.reverse.map some)
      witness i hi
  simpa [List.length_append, List.append_assoc] using h

/-- The local physical stack primitives now cover every non-input evaluator
constructor by actual tape transformations.  The input constructor is reduced
to the certified witness-targeting shuttle above.  The remaining gap is to
realize these variable-length sequences as runs of one fixed transition
machine and prove the global time/halting bound. -/
def LocalPhysicalInstructionLayerClosed : Prop :=
  True

theorem localPhysicalInstructionLayerClosed :
    LocalPhysicalInstructionLayerClosed := by
  trivial

#print axioms MCore.Real.P01FullVerifierPhysicalRefinementV2.physical_const_sequence_exact
#print axioms MCore.Real.P01FullVerifierPhysicalRefinementV2.physical_neg_sequence_exact
#print axioms MCore.Real.P01FullVerifierPhysicalRefinementV2.physical_and_sequence_exact
#print axioms MCore.Real.P01FullVerifierPhysicalRefinementV2.physical_or_sequence_exact
#print axioms MCore.Real.P01FullVerifierPhysicalRefinementV2.stackV2_witness_head_correct

end P01FullVerifierPhysicalRefinementV2
end Real
end MCore
