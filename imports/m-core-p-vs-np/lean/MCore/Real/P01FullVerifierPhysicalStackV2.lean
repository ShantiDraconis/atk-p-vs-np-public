import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalStackV2

open CanonicalFinalProof
open P01FullVerifierPhysicalShuttles

def physicalStackV2Tape
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat := 0) : Tape (Option Bool) :=
  { left :=
      stack.map some ++
        none :: source.reverse.map some ++ none :: witness.map some
    head := none
    right := List.replicate padding none }

def PhysicalStackRepV2
    (tape : Tape (Option Bool))
    (witness source : BitString)
    (stack : List Bool) : Prop :=
  exists padding : Nat,
    tape = physicalStackV2Tape witness source stack padding

theorem physicalStackV2_empty
    (witness source : BitString) :
    PhysicalStackRepV2
      (physicalStackV2Tape witness source [])
      witness source [] := by
  exact ⟨0, rfl⟩

theorem sourceEnd_to_stackV2
    (witness source : BitString) :
    Tape.move none .right (sourceEndTape witness source) =
      physicalStackV2Tape witness source [] := by
  simp [sourceEndTape, physicalStackV2Tape, Tape.move]

def pushStep (b : Bool) (t : Tape (Option Bool)) : Tape (Option Bool) :=
  Tape.move none .right (Tape.write t (some b))

theorem pushStep_correct
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat) (b : Bool) :
    pushStep b (physicalStackV2Tape witness source stack padding) =
      physicalStackV2Tape witness source (b :: stack)
        (padding - 1) := by
  cases padding with
  | zero =>
      simp [pushStep, physicalStackV2Tape, Tape.write, Tape.move]
  | succ n =>
      simp [pushStep, physicalStackV2Tape, Tape.write, Tape.move,
        Nat.succ_sub_one, List.replicate_succ]

def popEnter (t : Tape (Option Bool)) : Tape (Option Bool) :=
  Tape.move none .left t

def popErase (t : Tape (Option Bool)) : Tape (Option Bool) :=
  Tape.write t none

theorem popEnter_head
    (witness source : BitString)
    (v : Bool) (stack : List Bool)
    (padding : Nat) :
    (popEnter
      (physicalStackV2Tape witness source (v :: stack) padding)).head =
      some v := by
  simp [popEnter, physicalStackV2Tape, Tape.move]

theorem popErase_correct
    (witness source : BitString)
    (v : Bool) (stack : List Bool)
    (padding : Nat) :
    popErase
      (popEnter
        (physicalStackV2Tape witness source (v :: stack) padding)) =
      physicalStackV2Tape witness source stack (padding + 1) := by
  simp [popErase, popEnter, physicalStackV2Tape, Tape.write, Tape.move,
    List.map_cons, List.append_assoc, List.replicate_succ, Nat.add_comm]

theorem physicalStackRepV2_push
    {tape : Tape (Option Bool)}
    {witness source : BitString}
    {stack : List Bool}
    (b : Bool)
    (hrep : PhysicalStackRepV2 tape witness source stack) :
    PhysicalStackRepV2 (pushStep b tape) witness source (b :: stack) := by
  rcases hrep with ⟨padding, rfl⟩
  refine ⟨padding - 1, ?_⟩
  exact pushStep_correct witness source stack padding b

theorem physicalStackRepV2_pop
    {tape : Tape (Option Bool)}
    {witness source : BitString}
    {v : Bool} {stack : List Bool}
    (hrep : PhysicalStackRepV2 tape witness source (v :: stack)) :
    (popEnter tape).head = some v /\
      PhysicalStackRepV2 (popErase (popEnter tape))
        witness source stack := by
  rcases hrep with ⟨padding, rfl⟩
  constructor
  · exact popEnter_head witness source v stack padding
  · exact ⟨padding + 1, popErase_correct witness source v stack padding⟩

#print axioms MCore.Real.P01FullVerifierPhysicalStackV2.sourceEnd_to_stackV2
#print axioms MCore.Real.P01FullVerifierPhysicalStackV2.pushStep_correct
#print axioms MCore.Real.P01FullVerifierPhysicalStackV2.popErase_correct

end P01FullVerifierPhysicalStackV2
end Real
end MCore
