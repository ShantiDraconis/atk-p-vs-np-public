import MCore.Real.P02BoundedComputationEncoding

namespace MCore
namespace Real
namespace P02BoundedComputationTape

open CanonicalFinalProof
open P02BoundedComputationEncoding

theorem move_left_head_getD
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .left tape).head =
      tape.left.getD 0 blank := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_zero]

theorem move_left_left_getD
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol)
    (i : Nat) :
    (Tape.move blank .left tape).left.getD i blank =
      tape.left.getD (i + 1) blank := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_succ]

theorem move_left_right_zero
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .left tape).right.getD 0 blank =
      tape.head := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_zero]

theorem move_left_right_succ
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol)
    (i : Nat) :
    (Tape.move blank .left tape).right.getD (i + 1) blank =
      tape.right.getD i blank := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_succ]

theorem move_right_head_getD
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .right tape).head =
      tape.right.getD 0 blank := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.move, List.getD_cons_zero]

theorem move_right_right_getD
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol)
    (i : Nat) :
    (Tape.move blank .right tape).right.getD i blank =
      tape.right.getD (i + 1) blank := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.move, List.getD_cons_succ]

theorem move_right_left_zero
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .right tape).left.getD 0 blank =
      tape.head := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.move, List.getD_cons_zero]

theorem move_right_left_succ
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol)
    (i : Nat) :
    (Tape.move blank .right tape).left.getD (i + 1) blank =
      tape.left.getD i blank := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.move, List.getD_cons_succ]

theorem getD_eq_default_of_length_le
    {α : Type}
    (l : List α)
    (i : Nat)
    (d : α)
    (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none_iff.mpr h]

theorem move_left_length_le
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .left tape).left.length ≤ tape.left.length + 1 ∧
    (Tape.move blank .left tape).right.length ≤ tape.right.length + 1 := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.move] <;> omega

theorem move_right_length_le
    {Symbol : Type}
    (blank : Symbol)
    (tape : Tape Symbol) :
    (Tape.move blank .right tape).left.length ≤ tape.left.length + 1 ∧
    (Tape.move blank .right tape).right.length ≤ tape.right.length + 1 := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.move] <;> omega

theorem move_length_le
    {Symbol : Type}
    (blank : Symbol)
    (direction : Direction)
    (tape : Tape Symbol) :
    (Tape.move blank direction tape).left.length ≤ tape.left.length + 1 ∧
    (Tape.move blank direction tape).right.length ≤ tape.right.length + 1 := by
  cases direction with
  | left => exact move_left_length_le blank tape
  | stay => simp [Tape.move]
  | right => exact move_right_length_le blank tape

theorem step_tape_length_le
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config : Configuration State Symbol) :
    (machine.step config).tape.left.length ≤ config.tape.left.length + 1 ∧
    (machine.step config).tape.right.length ≤ config.tape.right.length + 1 := by
  unfold TM.step
  rcases htrans : machine.transition config.state config.tape.head with
    ⟨nextState, nextSymbol, direction⟩
  simp only [htrans]
  exact move_length_le machine.blank direction (config.tape.write nextSymbol)

theorem run_tape_length_le
    {State Symbol : Type}
    (machine : TM State Symbol)
    (fuel : Nat)
    (config : Configuration State Symbol) :
    (machine.run fuel config).tape.left.length ≤
        config.tape.left.length + fuel ∧
    (machine.run fuel config).tape.right.length ≤
        config.tape.right.length + fuel := by
  induction fuel generalizing config with
  | zero =>
      simp [TM.run]
  | succ fuel ih =>
      rw [TM.run]
      by_cases h : machine.halting config.state = true
      · simp [h]
      · have hf : machine.halting config.state = false := by
          cases hh : machine.halting config.state <;> simp_all
        simp only [hf, Bool.false_eq_true, if_false]
        have hr := ih (config := machine.step config)
        have hs := step_tape_length_le machine config
        constructor <;> omega

theorem inputTape_right_length_le
    (x : BitString) :
    (inputTape x).right.length ≤ x.length := by
  cases x <;> simp [inputTape]

theorem canonical_run_left_length_le
    (M : PolyDTMCandidate)
    (x : BitString)
    (s : Nat) :
    (M.machine.run s (initialTMConfig M.machine x)).tape.left.length ≤ s := by
  have h := (run_tape_length_le M.machine s
    (initialTMConfig M.machine x)).1
  have hz : (inputTape x).left.length = 0 := by
    cases x <;> rfl
  change
    (M.machine.run s
      { state := M.machine.initial, tape := inputTape x }).tape.left.length ≤ s
  change
    (M.machine.run s
      { state := M.machine.initial, tape := inputTape x }).tape.left.length ≤
        (inputTape x).left.length + s at h
  rw [hz] at h
  simpa using h

theorem canonical_run_right_length_le
    (M : PolyDTMCandidate)
    (x : BitString)
    (s : Nat) :
    (M.machine.run s (initialTMConfig M.machine x)).tape.right.length ≤
      x.length + s := by
  have h := (run_tape_length_le M.machine s
    (initialTMConfig M.machine x)).2
  have hinput := inputTape_right_length_le x
  change
    (M.machine.run s
      { state := M.machine.initial, tape := inputTape x }).tape.right.length ≤
        x.length + s
  change
    (M.machine.run s
      { state := M.machine.initial, tape := inputTape x }).tape.right.length ≤
        (inputTape x).right.length + s at h
  omega

theorem canonical_run_left_radius_blank
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s ≤ t) :
    (M.machine.run s (initialTMConfig M.machine x)).tape.left.getD
      (radius x t) M.machine.blank = M.machine.blank := by
  apply getD_eq_default_of_length_le
  have hlen := canonical_run_left_length_le M x s
  unfold radius
  omega

theorem canonical_run_right_radius_blank
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s ≤ t) :
    (M.machine.run s (initialTMConfig M.machine x)).tape.right.getD
      (radius x t) M.machine.blank = M.machine.blank := by
  apply getD_eq_default_of_length_le
  have hlen := canonical_run_right_length_le M x s
  unfold radius
  omega

#print axioms MCore.Real.P02BoundedComputationTape.move_left_left_getD
#print axioms MCore.Real.P02BoundedComputationTape.move_right_right_getD
#print axioms MCore.Real.P02BoundedComputationTape.run_tape_length_le
#print axioms MCore.Real.P02BoundedComputationTape.canonical_run_left_radius_blank
#print axioms MCore.Real.P02BoundedComputationTape.canonical_run_right_radius_blank

end P02BoundedComputationTape
end Real
end MCore
