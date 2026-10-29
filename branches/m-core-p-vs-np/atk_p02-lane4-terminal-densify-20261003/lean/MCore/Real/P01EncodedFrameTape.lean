import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01EncodedFrameTape

open CanonicalFinalProof
open P01EncodedStackEvaluator

/-- Fixed-width three-bit physical code for the seven semantic continuation
frames.  The code 111 is deliberately unused, giving a malformed-code reject
case to the future physical verifier. -/
def encodeEvalFrame : EvalFrame → BitString
  | .neg            => [false, false, false]
  | .andLeft        => [false, false, true]
  | .andRight false => [false, true, false]
  | .andRight true  => [false, true, true]
  | .orLeft         => [true, false, false]
  | .orRight false  => [true, false, true]
  | .orRight true   => [true, true, false]

def decodeEvalFrame : BitString → Option EvalFrame
  | [false, false, false] => some .neg
  | [false, false, true]  => some .andLeft
  | [false, true, false]  => some (.andRight false)
  | [false, true, true]   => some (.andRight true)
  | [true, false, false]  => some .orLeft
  | [true, false, true]   => some (.orRight false)
  | [true, true, false]   => some (.orRight true)
  | _ => none

@[simp] theorem decodeEvalFrame_encodeEvalFrame
    (f : EvalFrame) :
    decodeEvalFrame (encodeEvalFrame f) = some f := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

@[simp] theorem encodeEvalFrame_length
    (f : EvalFrame) :
    (encodeEvalFrame f).length = 3 := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

theorem encodeEvalFrame_injective :
    ∀ ⦃a b : EvalFrame⦄,
      encodeEvalFrame a = encodeEvalFrame b → a = b := by
  intro a b h
  have hd := congrArg decodeEvalFrame h
  simpa using hd

/-- Concatenated fixed-width representation of the continuation stack. -/
def encodeEvalFrames : List EvalFrame → BitString
  | [] => []
  | f :: fs => encodeEvalFrame f ++ encodeEvalFrames fs

@[simp] theorem encodeEvalFrames_nil :
    encodeEvalFrames [] = [] := rfl

@[simp] theorem encodeEvalFrames_cons
    (f : EvalFrame) (fs : List EvalFrame) :
    encodeEvalFrames (f :: fs) =
      encodeEvalFrame f ++ encodeEvalFrames fs := rfl

theorem encodeEvalFrames_length
    (fs : List EvalFrame) :
    (encodeEvalFrames fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [encodeEvalFrames, encodeEvalFrame_length, ih]
      omega

/-- Decode a full stack in three-bit blocks.  Any malformed/truncated code
fails rather than silently manufacturing a frame. -/
def decodeEvalFrames : BitString → Option (List EvalFrame)
  | [] => some []
  | a :: b :: c :: rest => do
      let f ← decodeEvalFrame [a,b,c]
      let fs ← decodeEvalFrames rest
      some (f :: fs)
  | _ => none

@[simp] theorem decodeEvalFrames_encodeEvalFrames
    (fs : List EvalFrame) :
    decodeEvalFrames (encodeEvalFrames fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | neg =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | andLeft =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | andRight b =>
          cases b <;>
            simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
              decodeEvalFrame, ih]
      | orLeft =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | orRight b =>
          cases b <;>
            simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
              decodeEvalFrame, ih]

/-- The frame stack consumes at most three tape cells per semantic frame. -/
theorem encodedFrames_linear_space
    (fs : List EvalFrame) (n : Nat)
    (h : fs.length ≤ n) :
    (encodeEvalFrames fs).length ≤ 3 * n := by
  rw [encodeEvalFrames_length]
  exact Nat.mul_le_mul_left 3 h

#print axioms MCore.Real.P01EncodedFrameTape.decodeEvalFrame_encodeEvalFrame
#print axioms MCore.Real.P01EncodedFrameTape.encodeEvalFrame_injective
#print axioms MCore.Real.P01EncodedFrameTape.decodeEvalFrames_encodeEvalFrames
#print axioms MCore.Real.P01EncodedFrameTape.encodedFrames_linear_space

end P01EncodedFrameTape
end Real
end MCore
