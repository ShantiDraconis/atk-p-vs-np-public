import MCore.Real.P01EncodedEvaluator

namespace MCore
namespace Real
namespace P01EncodedStackEvaluator

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01EncodedEvaluator

/-- Finite continuation alphabet for direct prefix evaluation.
The only stored Boolean is the already-computed left operand of a binary node. -/
inductive EvalFrame where
  | neg
  | andLeft
  | andRight : Bool → EvalFrame
  | orLeft
  | orRight : Bool → EvalFrame
  deriving DecidableEq, Repr

/-- Explicit streaming evaluator state.  `value = none` means the next prefix
expression must be consumed; `some v` means a value is returning through the
continuation stack. -/
structure EvalState where
  bits : BitString
  frames : List EvalFrame
  value : Option Bool
  deriving Repr

def needExpr (bits : BitString) (frames : List EvalFrame := []) : EvalState :=
  { bits := bits, frames := frames, value := none }

def haveValue
    (v : Bool) (bits : BitString) (frames : List EvalFrame := []) : EvalState :=
  { bits := bits, frames := frames, value := some v }

/-- One semantic control transition of the iterative evaluator.  Tags and unary
indices are consumed from the bitstream; recursive structure is represented
only by the finite frame alphabet. -/
def evalStep (sigma : Assignment) : EvalState → Option EvalState
  | { bits := bits, frames := frames, value := none } =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (haveValue (sigma i) tail frames)
          | none => none
      | false :: false :: true :: rest =>
          some (haveValue false rest frames)
      | false :: true :: false :: rest =>
          some (haveValue true rest frames)
      | false :: true :: true :: rest =>
          some (needExpr rest (.neg :: frames))
      | true :: false :: false :: rest =>
          some (needExpr rest (.andLeft :: frames))
      | true :: false :: true :: rest =>
          some (needExpr rest (.orLeft :: frames))
      | _ => none
  | { bits := bits, frames := [], value := some _ } =>
      none
  | { bits := bits, frames := .neg :: frames, value := some v } =>
      some (haveValue (!v) bits frames)
  | { bits := bits, frames := .andLeft :: frames, value := some l } =>
      some (needExpr bits (.andRight l :: frames))
  | { bits := bits, frames := .andRight l :: frames, value := some r } =>
      some (haveValue (Bool.and l r) bits frames)
  | { bits := bits, frames := .orLeft :: frames, value := some l } =>
      some (needExpr bits (.orRight l :: frames))
  | { bits := bits, frames := .orRight l :: frames, value := some r } =>
      some (haveValue (Bool.or l r) bits frames)

/-- Iterate the finite-control semantics.  A halted/error state is stable under
additional fuel. -/
def evalRun : Nat → Assignment → EvalState → EvalState
  | 0, _, s => s
  | fuel + 1, sigma, s =>
      match evalStep sigma s with
      | none => s
      | some s' => evalRun fuel sigma s'

theorem evalRun_of_step_none
    (n : Nat) (sigma : Assignment) (s : EvalState)
    (h : evalStep sigma s = none) :
    evalRun n sigma s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evalRun, h]

theorem evalRun_add
    (m n : Nat) (sigma : Assignment) (s : EvalState) :
    evalRun (m + n) sigma s =
      evalRun n sigma (evalRun m sigma s) := by
  induction m generalizing s with
  | zero =>
      simp [evalRun]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [evalRun]
      cases h : evalStep sigma s with
      | none =>
          change s = evalRun n sigma s
          exact (evalRun_of_step_none n sigma s h).symm
      | some s' =>
          change evalRun (m + n) sigma s' =
            evalRun n sigma (evalRun m sigma s')
          exact ih s'

theorem evalRun_halted
    (n : Nat) (sigma : Assignment) (v : Bool) (bits : BitString) :
    evalRun n sigma (haveValue v bits []) =
      haveValue v bits [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evalRun, evalStep, haveValue, ih]

/-- Exact number of semantic control transitions required by one encoded
circuit, independent of the external tail and continuation. -/
def evalStepCount : Circuit → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => 1 + evalStepCount c + 1
  | .and a b => 1 + evalStepCount a + 1 + evalStepCount b + 1
  | .or a b => 1 + evalStepCount a + 1 + evalStepCount b + 1

/-- Main continuation theorem: after exactly `evalStepCount c` transitions,
the encoded circuit has been consumed, the external tail is untouched, the
original continuation stack is restored, and the exact semantic value is
available. -/
theorem evalRun_encode_append
    (sigma : Assignment)
    (c : Circuit)
    (tail : BitString)
    (frames : List EvalFrame) :
    evalRun (evalStepCount c) sigma
        (needExpr (encodeCircuit c ++ tail) frames) =
      haveValue (evalCircuit sigma c) tail frames := by
  induction c generalizing tail frames with
  | input i =>
      simp [evalStepCount, evalRun, evalStep, needExpr, haveValue,
        encodeCircuit, decodeNat_encodeNat_append, evalCircuit]
  | const b =>
      cases b <;>
        simp [evalStepCount, evalRun, evalStep, needExpr, haveValue,
          encodeCircuit, evalCircuit]
  | not c ih =>
      rw [show evalStepCount (.not c) =
          1 + (evalStepCount c + 1) by
            simp [evalStepCount, Nat.add_assoc]]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.not c) ++ tail) frames) =
            needExpr (encodeCircuit c ++ tail) (.neg :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [ih (tail := tail) (frames := .neg :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]
  | and a b iha ihb =>
      rw [show evalStepCount (.and a b) =
          1 + (evalStepCount a +
            (1 + (evalStepCount b + 1))) by
            simp [evalStepCount]; omega]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.and a b) ++ tail) frames) =
            needExpr
              (encodeCircuit a ++ (encodeCircuit b ++ tail))
              (.andLeft :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [iha
        (tail := encodeCircuit b ++ tail)
        (frames := .andLeft :: frames)]
      rw [evalRun_add]
      have hleft :
          evalRun 1 sigma
              (haveValue (evalCircuit sigma a)
                (encodeCircuit b ++ tail) (.andLeft :: frames)) =
            needExpr (encodeCircuit b ++ tail)
              (.andRight (evalCircuit sigma a) :: frames) := by
        rfl
      rw [hleft]
      rw [evalRun_add]
      rw [ihb
        (tail := tail)
        (frames := .andRight (evalCircuit sigma a) :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]
  | or a b iha ihb =>
      rw [show evalStepCount (.or a b) =
          1 + (evalStepCount a +
            (1 + (evalStepCount b + 1))) by
            simp [evalStepCount]; omega]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.or a b) ++ tail) frames) =
            needExpr
              (encodeCircuit a ++ (encodeCircuit b ++ tail))
              (.orLeft :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [iha
        (tail := encodeCircuit b ++ tail)
        (frames := .orLeft :: frames)]
      rw [evalRun_add]
      have hleft :
          evalRun 1 sigma
              (haveValue (evalCircuit sigma a)
                (encodeCircuit b ++ tail) (.orLeft :: frames)) =
            needExpr (encodeCircuit b ++ tail)
              (.orRight (evalCircuit sigma a) :: frames) := by
        rfl
      rw [hleft]
      rw [evalRun_add]
      rw [ihb
        (tail := tail)
        (frames := .orRight (evalCircuit sigma a) :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]

/-- The explicit control-step count is linear in circuit size. -/
theorem evalStepCount_le_three_mul_size
    (c : Circuit) :
    evalStepCount c ≤ 3 * CircuitK1.size c := by
  induction c with
  | input i =>
      simp [evalStepCount, CircuitK1.size]
  | const b =>
      simp [evalStepCount, CircuitK1.size]
  | not c ih =>
      simp [evalStepCount, CircuitK1.size] at *
      omega
  | and a b iha ihb =>
      simp [evalStepCount, CircuitK1.size] at *
      omega
  | or a b iha ihb =>
      simp [evalStepCount, CircuitK1.size] at *
      omega

theorem evalStepCount_le_three_mul_encoding
    (c : Circuit) :
    evalStepCount c ≤ 3 * (encodeCircuit c).length := by
  exact Nat.le_trans
    (evalStepCount_le_three_mul_size c)
    (Nat.mul_le_mul_left 3 (size_le_encodeCircuit_length c))

/-- Extra fuel after successful evaluation is inert, so a bound depending only
on encoded input length suffices. -/
theorem evalRun_encode_bounded
    (sigma : Assignment)
    (c : Circuit) :
    evalRun (3 * (encodeCircuit c).length) sigma
        (needExpr (encodeCircuit c) []) =
      haveValue (evalCircuit sigma c) [] [] := by
  have hle := evalStepCount_le_three_mul_encoding c
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, evalRun_add]
  rw [show encodeCircuit c = encodeCircuit c ++ [] by simp]
  rw [evalRun_encode_append]
  exact evalRun_halted k sigma (evalCircuit sigma c) []

#print axioms MCore.Real.P01EncodedStackEvaluator.evalRun_encode_append
#print axioms MCore.Real.P01EncodedStackEvaluator.evalStepCount_le_three_mul_encoding
#print axioms MCore.Real.P01EncodedStackEvaluator.evalRun_encode_bounded

end P01EncodedStackEvaluator
end Real
end MCore
