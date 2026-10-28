import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01BinaryLayoutConservation

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01CheckedVerifierInvariant

/--
Exact layout handed to the child of a NOT after consuming the root tag and
pushing the negation continuation frame.
-/
theorem not_child_layout
    (n consumed : Nat)
    (child : CircuitK1.Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit (.not child) ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n (consumed + 3)
      (encodeCircuit child ++ tail)
      (encodeEvalFrame .neg ++ encodeEvalFrames frames) := by
  have h0 :
      CheckedLayoutBound n consumed
        (false :: true :: true :: (encodeCircuit child ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using h
  exact after_push_tag n consumed false true true
    (encodeCircuit child ++ tail) (encodeEvalFrames frames) .neg h0

/-- Exact left-child layout of AND after the root tag and left frame push. -/
theorem and_left_layout
    (n consumed : Nat)
    (left right : CircuitK1.Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit (.and left right) ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n (consumed + 3)
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
  have h0 :
      CheckedLayoutBound n consumed
        (true :: false :: false ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using h
  exact after_push_tag n consumed true false false
    (encodeCircuit left ++ encodeCircuit right ++ tail)
    (encodeEvalFrames frames) .andLeft h0

/-- Exact left-child layout of OR after the root tag and left frame push. -/
theorem or_left_layout
    (n consumed : Nat)
    (left right : CircuitK1.Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit (.or left right) ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n (consumed + 3)
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
  have h0 :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using h
  exact after_push_tag n consumed true false true
    (encodeCircuit left ++ encodeCircuit right ++ tail)
    (encodeEvalFrames frames) .orLeft h0

/--
Exact layout handed to the right child of an AND after the root tag is
consumed, the left child is fully consumed, and the continuation frame is
replaced by its value-carrying right frame.
-/
theorem and_right_layout
    (n consumed : Nat)
    (left right : CircuitK1.Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (leftValue : Bool)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit (.and left right) ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n
      (consumed + 3 + (encodeCircuit left).length)
      (encodeCircuit right ++ tail)
      (encodeEvalFrame (.andRight leftValue) ++ encodeEvalFrames frames) := by
  have h0 :
      CheckedLayoutBound n consumed
        (true :: false :: false ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using h
  have h1 :=
    after_push_tag n consumed true false false
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) .andLeft h0
  have h2 :=
    after_exact_circuit n (consumed + 3) left
      (encodeCircuit right ++ tail)
      (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) h1
  have h3 :=
    replace_top_frame_exact n
      (consumed + 3 + (encodeCircuit left).length)
      (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      .andLeft (.andRight leftValue) h2
  exact h3

/--
Exact layout handed to the right child of an OR.  The proof is the same
conservation law, with the OR continuation frame replacing the left frame.
-/
theorem or_right_layout
    (n consumed : Nat)
    (left right : CircuitK1.Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (leftValue : Bool)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit (.or left right) ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n
      (consumed + 3 + (encodeCircuit left).length)
      (encodeCircuit right ++ tail)
      (encodeEvalFrame (.orRight leftValue) ++ encodeEvalFrames frames) := by
  have h0 :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using h
  have h1 :=
    after_push_tag n consumed true false true
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) .orLeft h0
  have h2 :=
    after_exact_circuit n (consumed + 3) left
      (encodeCircuit right ++ tail)
      (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) h1
  have h3 :=
    replace_top_frame_exact n
      (consumed + 3 + (encodeCircuit left).length)
      (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      .orLeft (.orRight leftValue) h2
  exact h3

/-- Exact consumed counter after a complete NOT prefix. -/
theorem not_consumed_arithmetic
    (consumed : Nat)
    (child : CircuitK1.Circuit) :
    consumed + 3 + (encodeCircuit child).length =
      consumed + (encodeCircuit (.not child)).length := by
  simp [encodeCircuit, List.length_append]
  omega

/-- Exact consumed counter after a complete binary prefix. -/
theorem and_consumed_arithmetic
    (consumed : Nat)
    (left right : CircuitK1.Circuit) :
    consumed + 3 + (encodeCircuit left).length +
        (encodeCircuit right).length =
      consumed + (encodeCircuit (.and left right)).length := by
  simp [encodeCircuit, List.length_append]
  omega

/-- Exact consumed counter after a complete OR prefix. -/
theorem or_consumed_arithmetic
    (consumed : Nat)
    (left right : CircuitK1.Circuit) :
    consumed + 3 + (encodeCircuit left).length +
        (encodeCircuit right).length =
      consumed + (encodeCircuit (.or left right)).length := by
  simp [encodeCircuit, List.length_append]
  omega

#print axioms MCore.Real.P01BinaryLayoutConservation.not_child_layout
#print axioms MCore.Real.P01BinaryLayoutConservation.and_left_layout
#print axioms MCore.Real.P01BinaryLayoutConservation.or_left_layout
#print axioms MCore.Real.P01BinaryLayoutConservation.and_right_layout
#print axioms MCore.Real.P01BinaryLayoutConservation.or_right_layout
#print axioms MCore.Real.P01BinaryLayoutConservation.not_consumed_arithmetic
#print axioms MCore.Real.P01BinaryLayoutConservation.and_consumed_arithmetic
#print axioms MCore.Real.P01BinaryLayoutConservation.or_consumed_arithmetic

end P01BinaryLayoutConservation
end Real
end MCore
