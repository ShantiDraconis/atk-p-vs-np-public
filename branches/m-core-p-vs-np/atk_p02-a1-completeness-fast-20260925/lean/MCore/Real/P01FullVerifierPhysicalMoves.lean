import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalMoves

open CanonicalFinalProof

/-- Execute a finite sequence of legal single-cell head moves without writing.
This is the concrete replacement for pseudo-operations such as moveToWitness
and moveToStack. -/
def execMoves {Symbol : Type}
    (blank : Symbol) : List Direction → Tape Symbol → Tape Symbol
  | [], tape => tape
  | d :: ds, tape => execMoves blank ds (Tape.move blank d tape)

def moveLeftSeq (n : Nat) : List Direction :=
  List.replicate n .left

def moveRightSeq (n : Nat) : List Direction :=
  List.replicate n .right

@[simp] theorem execMoves_nil {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol) :
    execMoves blank [] t = t := rfl

@[simp] theorem execMoves_cons {Symbol : Type}
    (blank : Symbol) (d : Direction) (ds : List Direction) (t : Tape Symbol) :
    execMoves blank (d :: ds) t =
      execMoves blank ds (Tape.move blank d t) := rfl

theorem moveLeftSeq_length (n : Nat) :
    (moveLeftSeq n).length = n := by
  simp [moveLeftSeq]

theorem moveRightSeq_length (n : Nat) :
    (moveRightSeq n).length = n := by
  simp [moveRightSeq]

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

/-- Canonical finite iteration of one primitive tape move. -/
def repeatMove {Symbol : Type}
    (blank : Symbol) (d : Direction) (n : Nat) (t : Tape Symbol) : Tape Symbol :=
  execMoves blank (List.replicate n d) t

/-- Repeated left motion is exactly the canonical primitive-move iteration. -/
theorem execMoves_moveLeftSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveLeftSeq n) t =
      repeatMove blank .left n t := by
  rfl

/-- Repeated right motion is exactly the canonical primitive-move iteration. -/
theorem execMoves_moveRightSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveRightSeq n) t =
      repeatMove blank .right n t := by
  rfl

theorem move_left_left_getD {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol) (n : Nat) :
    (Tape.move blank .left t).left.getD n blank =
      t.left.getD (n + 1) blank := by
  cases t with
  | mk left head right =>
      cases left <;> simp [Tape.move, List.getD_cons_succ]


/-- After n+1 left moves, the head contains the n-th cell of the original
left list, defaulting to blank beyond its end. -/
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

/-- Every shuttle used by the verifier is built solely from legal TM moves. -/
def LegalMoveSeq (ds : List Direction) : Prop :=
  ∀ d ∈ ds, d = .left ∨ d = .right ∨ d = .stay

theorem moveLeftSeq_legal (n : Nat) : LegalMoveSeq (moveLeftSeq n) := by
  intro d hd
  exact Or.inl (moveLeftSeq_all_legal n d hd)

theorem moveRightSeq_legal (n : Nat) : LegalMoveSeq (moveRightSeq n) := by
  intro d hd
  exact Or.inr (Or.inl (moveRightSeq_all_legal n d hd))

/-- Abstract physical shuttle certificate.  Target location is a predicate on
the resulting tape, keeping positional arithmetic on tape rather than finite
control. -/
structure ShuttleCertificate
    (start : Tape (Option Bool))
    (target : Tape (Option Bool) → Prop) where
  moves : List Direction
  legal : LegalMoveSeq moves
  reaches : target (execMoves none moves start)

#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveLeftSeq
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveRightSeq
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveLeftSeq_head_getD
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.moveLeftSeq_legal
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.moveRightSeq_legal

end P01FullVerifierPhysicalMoves
end Real
end MCore
