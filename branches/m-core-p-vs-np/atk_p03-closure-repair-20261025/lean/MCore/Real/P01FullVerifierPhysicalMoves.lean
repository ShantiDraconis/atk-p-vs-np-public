import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalMoves

open CanonicalFinalProof

def execMoves {Symbol : Type}
    (blank : Symbol) : List Direction → Tape Symbol → Tape Symbol
  | [], tape => tape
  | d :: ds, tape => execMoves blank ds (Tape.move blank d tape)

def moveLeftSeq (n : Nat) : List Direction := List.replicate n .left
def moveRightSeq (n : Nat) : List Direction := List.replicate n .right

@[simp] theorem execMoves_nil {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol) :
    execMoves blank [] t = t := rfl

@[simp] theorem execMoves_cons {Symbol : Type}
    (blank : Symbol) (d : Direction) (ds : List Direction) (t : Tape Symbol) :
    execMoves blank (d :: ds) t =
      execMoves blank ds (Tape.move blank d t) := rfl

theorem moveLeftSeq_length (n : Nat) :
    (moveLeftSeq n).length = n := by simp [moveLeftSeq]

theorem moveRightSeq_length (n : Nat) :
    (moveRightSeq n).length = n := by simp [moveRightSeq]

theorem moveLeftSeq_all_legal (n : Nat) :
    ∀ d ∈ moveLeftSeq n, d = .left := by
  induction n with
  | zero =>
      simp [moveLeftSeq]
  | succ n ih =>
      intro d hd
      simp only [moveLeftSeq, List.replicate_succ, List.mem_cons] at hd
      rcases hd with h | h
      · exact h
      · exact ih d h

theorem moveRightSeq_all_legal (n : Nat) :
    ∀ d ∈ moveRightSeq n, d = .right := by
  induction n with
  | zero =>
      simp [moveRightSeq]
  | succ n ih =>
      intro d hd
      simp only [moveRightSeq, List.replicate_succ, List.mem_cons] at hd
      rcases hd with h | h
      · exact h
      · exact ih d h

def repeatMove {Symbol : Type}
    (blank : Symbol) (d : Direction) (n : Nat) (t : Tape Symbol) : Tape Symbol :=
  execMoves blank (List.replicate n d) t

theorem execMoves_moveLeftSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveLeftSeq n) t =
      repeatMove blank .left n t := by rfl

theorem execMoves_moveRightSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveRightSeq n) t =
      repeatMove blank .right n t := by rfl

theorem move_left_left_getD {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol) (n : Nat) :
    (Tape.move blank .left t).left.getD n blank =
      t.left.getD (n + 1) blank := by
  cases t with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_succ]

theorem execMoves_moveLeftSeq_head_getD {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    (execMoves blank (moveLeftSeq (n + 1)) t).head =
      t.left.getD n blank := by
  induction n generalizing t with
  | zero =>
      cases t with
      | mk left head right =>
          cases left <;>
            simp [moveLeftSeq, execMoves, Tape.move, List.getD_cons_zero]
  | succ n ih =>
      have hstep :
          execMoves blank (moveLeftSeq (Nat.succ n + 1)) t =
            execMoves blank (moveLeftSeq (n + 1))
              (Tape.move blank .left t) := by
        simp [moveLeftSeq, List.replicate_succ, execMoves]
      rw [hstep, ih, move_left_left_getD]

def LegalMoveSeq (ds : List Direction) : Prop :=
  ∀ d ∈ ds, d = .left ∨ d = .right ∨ d = .stay

theorem moveLeftSeq_legal (n : Nat) : LegalMoveSeq (moveLeftSeq n) := by
  intro d hd
  exact Or.inl (moveLeftSeq_all_legal n d hd)

theorem moveRightSeq_legal (n : Nat) : LegalMoveSeq (moveRightSeq n) := by
  intro d hd
  exact Or.inr (Or.inl (moveRightSeq_all_legal n d hd))

end P01FullVerifierPhysicalMoves
end Real
end MCore
