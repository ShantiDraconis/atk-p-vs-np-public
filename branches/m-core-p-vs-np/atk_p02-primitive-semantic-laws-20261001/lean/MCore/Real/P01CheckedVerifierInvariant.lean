import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01InputNodeRoundTrip

namespace MCore
namespace Real
namespace P01CheckedVerifierInvariant

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01InputNodeRoundTrip
open P01CheckedVerifierBudget

structure CheckedLayoutBound
    (n consumed : Nat)
    (source frameStack : BitString) : Prop where
  source_budget : consumed + source.length ≤ n
  frames_paid : frameStack.length ≤ consumed

theorem CheckedLayoutBound.consumed_le
    {n consumed : Nat} {source frameStack : BitString}
    (h : CheckedLayoutBound n consumed source frameStack) :
    consumed ≤ n := by
  have hs := h.source_budget
  omega

theorem CheckedLayoutBound.source_le
    {n consumed : Nat} {source frameStack : BitString}
    (h : CheckedLayoutBound n consumed source frameStack) :
    source.length ≤ n := by
  have hs := h.source_budget
  omega

theorem CheckedLayoutBound.frames_le
    {n consumed : Nat} {source frameStack : BitString}
    (h : CheckedLayoutBound n consumed source frameStack) :
    frameStack.length ≤ n := by
  exact Nat.le_trans h.frames_paid h.consumed_le

theorem after_tag
    (n consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) frameStack) :
    CheckedLayoutBound n (consumed + 3) rest frameStack := by
  constructor
  · have hs := h.source_budget
    simp at hs
    omega
  · have hf := h.frames_paid
    omega

theorem after_push_tag
    (n consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest frameStack : BitString)
    (frame : EvalFrame)
    (h :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) frameStack) :
    CheckedLayoutBound n (consumed + 3) rest
      (encodeEvalFrame frame ++ frameStack) := by
  constructor
  · have hs := h.source_budget
    simp at hs
    omega
  · have hf := h.frames_paid
    rw [List.length_append, encodeEvalFrame_length]
    omega

theorem after_input
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        frameStack) :
    CheckedLayoutBound n
      (consumedAfterInputIndex (consumed + 3) i)
      tail frameStack := by
  constructor
  · have hs := h.source_budget
    simp [List.length_append, encodeNat_length] at hs
    unfold consumedAfterInputIndex
    omega
  · have hf := h.frames_paid
    unfold consumedAfterInputIndex
    omega

theorem replace_top_frame
    (n consumed : Nat)
    (source frameStack : BitString)
    (oldFrame newFrame : EvalFrame)
    (h :
      CheckedLayoutBound n consumed source
        (encodeEvalFrame oldFrame ++ frameStack)) :
    CheckedLayoutBound n consumed source
      (encodeEvalFrame newFrame ++ frameStack) := by
  constructor
  · exact h.source_budget
  · simpa [List.length_append, encodeEvalFrame_length] using h.frames_paid

theorem pop_frame
    (n consumed : Nat)
    (source frameStack : BitString)
    (frame : EvalFrame)
    (h :
      CheckedLayoutBound n consumed source
        (encodeEvalFrame frame ++ frameStack)) :
    CheckedLayoutBound n consumed source frameStack := by
  constructor
  · exact h.source_budget
  · have hlen := h.frames_paid
    rw [List.length_append, encodeEvalFrame_length] at hlen
    omega

theorem consumed_add_three_le
    (n consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) frameStack) :
    consumed + 3 ≤ n := by
  have hs := h.source_budget
  simp at hs
  omega

theorem input_index_le
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        frameStack) :
    i ≤ n := by
  have hs := h.source_budget
  simp [List.length_append, encodeNat_length] at hs
  omega

theorem root
    (source : BitString) :
    CheckedLayoutBound source.length 0 source [] := by
  constructor <;> simp

#print axioms MCore.Real.P01CheckedVerifierInvariant.after_tag
#print axioms MCore.Real.P01CheckedVerifierInvariant.after_push_tag
#print axioms MCore.Real.P01CheckedVerifierInvariant.after_input
#print axioms MCore.Real.P01CheckedVerifierInvariant.replace_top_frame
#print axioms MCore.Real.P01CheckedVerifierInvariant.pop_frame
#print axioms MCore.Real.P01CheckedVerifierInvariant.consumed_add_three_le
#print axioms MCore.Real.P01CheckedVerifierInvariant.input_index_le

end P01CheckedVerifierInvariant
end Real
end MCore
