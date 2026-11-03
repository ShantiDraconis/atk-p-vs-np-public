import MCore.Real.P01RawRecursiveSteps
import MCore.Real.P01RawDecodeFailureDescent
import MCore.Real.P01RawDecoderSound

namespace MCore
namespace Real
namespace P01RawRecursiveClosure

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01CheckedVerifierInvariant
open P01RawDecodeFailureShape
open P01RawDecodeFailureDescent
open P01RawDecoderSound
open P01RawEvalSink
open P01RawRecursiveSteps
open P01RawRecursiveBudget

/-- The exact recursive closure theorem.

The extra premise bits.length < fuel is not an assumption about the language:
it is definitionally true at the whole-source decoder call, where
fuel = bits.length + 1. It removes the unreachable fuelZero branch and gives
the well-founded descent needed by the five recursive constructors. -/
theorem rawDecodeFailure_reaches_sink :
    ∀ (fuel : Nat) (bits : BitString),
      RawDecodeFailure fuel bits →
      bits.length < fuel →
      ∀ (n : Nat) (mode : SyntaxMode)
        (witness : BitString) (frames : List EvalFrame)
        (consumed padding : Nat),
        witness.length = n →
        CheckedLayoutBound n consumed bits
          (encodeEvalFrames frames) →
        RawSinkCertificate fuel n mode witness bits frames
          consumed padding := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits hfail hlen
      omega
  | succ fuel ih =>
      intro bits hfail hlen n mode witness frames consumed padding hw hLayout
      cases hfail with
      | fuelZero bits =>
          omega
      | short0 f =>
          apply chunk_sink_to_succ fuel n mode witness [] frames consumed padding
          exact truncated_tag_reaches_sink
            n mode witness [] frames consumed padding
            (by decide) hLayout
      | short1 f b0 =>
          apply chunk_sink_to_succ fuel n mode witness [b0] frames consumed padding
          exact truncated_tag_reaches_sink
            n mode witness [b0] frames consumed padding
            (by decide) hLayout
      | short2 f b0 b1 =>
          apply chunk_sink_to_succ fuel n mode witness [b0, b1] frames consumed padding
          exact truncated_tag_reaches_sink
            n mode witness [b0, b1] frames consumed padding
            (by decide) hLayout
      | invalid110 f rest =>
          apply chunk_sink_to_succ fuel n mode witness
            (true :: true :: false :: rest) frames consumed padding
          exact disallowed_tag_reaches_sink
            n mode witness rest frames consumed padding
            true true false
            (by cases mode <;> rfl)
            hLayout
      | invalid111 f rest =>
          apply chunk_sink_to_succ fuel n mode witness
            (true :: true :: true :: rest) frames consumed padding
          exact disallowed_tag_reaches_sink
            n mode witness rest frames consumed padding
            true true true
            (by cases mode <;> rfl)
            hLayout
      | inputUnary f rest hnone =>
          apply chunk_sink_to_succ fuel n mode witness
            (false :: false :: false :: rest) frames consumed padding
          exact unary_none_reaches_sink
            n mode witness rest frames consumed padding hnone hLayout
      | notChild f rest hnone =>
          have hchildFail :
              RawDecodeFailure fuel rest :=
            rawDecodeFailure_of_none fuel rest hnone
          have hchildLen : rest.length < fuel := by
            simp at hlen
            omega
          have hLayoutChild :
              CheckedLayoutBound n (consumed + 3) rest
                (encodeEvalFrames (.neg :: frames)) := by
            have h :=
              P01CheckedVerifierInvariant.after_push_tag
                n consumed false true true rest
                (encodeEvalFrames frames) .neg hLayout
            simpa [encodeEvalFrames, List.append_assoc] using h
          have hrec :
              RawSinkCertificate fuel n (childMode mode .neg)
                witness rest (.neg :: frames) (consumed + 3)
                (((padding - 1) - 1) - 1) :=
            ih rest hchildFail hchildLen n (childMode mode .neg)
              witness (.neg :: frames) (consumed + 3)
              (((padding - 1) - 1) - 1) hw hLayoutChild
          exact not_child_failure_step
            fuel n mode witness rest frames consumed padding
            hLayout hrec
      | andLeft f rest hnone =>
          have hchildFail :
              RawDecodeFailure fuel rest :=
            rawDecodeFailure_of_none fuel rest hnone
          have hchildLen : rest.length < fuel := by
            simp at hlen
            omega
          have hLayoutChild :
              CheckedLayoutBound n (consumed + 3) rest
                (encodeEvalFrames (.andLeft :: frames)) := by
            have h :=
              P01CheckedVerifierInvariant.after_push_tag
                n consumed true false false rest
                (encodeEvalFrames frames) .andLeft hLayout
            simpa [encodeEvalFrames, List.append_assoc] using h
          have hrec :
              RawSinkCertificate fuel n .cnf
                witness rest (.andLeft :: frames) (consumed + 3)
                (((padding - 1) - 1) - 1) :=
            ih rest hchildFail hchildLen n .cnf witness
              (.andLeft :: frames) (consumed + 3)
              (((padding - 1) - 1) - 1) hw hLayoutChild
          exact and_left_failure_step
            fuel n mode witness rest frames consumed padding
            hLayout hrec
      | orLeft f rest hnone =>
          have hchildFail :
              RawDecodeFailure fuel rest :=
            rawDecodeFailure_of_none fuel rest hnone
          have hchildLen : rest.length < fuel := by
            simp at hlen
            omega
          have hLayoutChild :
              CheckedLayoutBound n (consumed + 3) rest
                (encodeEvalFrames (.orLeft :: frames)) := by
            have h :=
              P01CheckedVerifierInvariant.after_push_tag
                n consumed true false true rest
                (encodeEvalFrames frames) .orLeft hLayout
            simpa [encodeEvalFrames, List.append_assoc] using h
          have hrec :
              RawSinkCertificate fuel n .clause
                witness rest (.orLeft :: frames) (consumed + 3)
                (((padding - 1) - 1) - 1) :=
            ih rest hchildFail hchildLen n .clause witness
              (.orLeft :: frames) (consumed + 3)
              (((padding - 1) - 1) - 1) hw hLayoutChild
          exact or_left_failure_step
            fuel n mode witness rest frames consumed padding
            hLayout hrec
      | andRight f rest left rightSource hleft hright =>
          have hsrc :
              rest = encodeCircuit left ++ rightSource :=
            decodeCircuitCore_success_sound
              fuel rest left rightSource hleft
          have hchildFail :
              RawDecodeFailure fuel rightSource :=
            rawDecodeFailure_of_none fuel rightSource hright
          have hrightLen : rightSource.length < fuel := by
            have henc := three_le_encodeCircuit_length left
            rw [hsrc] at hlen
            simp [List.length_append] at hlen
            omega
          have hLayout' :
              CheckedLayoutBound n consumed
                (true :: false :: false ::
                  (encodeCircuit left ++ rightSource))
                (encodeEvalFrames frames) := by
            simpa [hsrc] using hLayout
          have hrec :
              ∀ (padRight : Nat),
                CheckedLayoutBound n
                  (consumed + 3 + (encodeCircuit left).length)
                  rightSource
                  (encodeEvalFrames
                    (.andRight
                      (CircuitK1.evalCircuit
                        (CanonicalSATWitness.witnessAssignment witness)
                        left) :: frames)) →
                RawSinkCertificate fuel n .cnf witness rightSource
                  (.andRight
                    (CircuitK1.evalCircuit
                      (CanonicalSATWitness.witnessAssignment witness)
                      left) :: frames)
                  (consumed + 3 + (encodeCircuit left).length)
                  padRight := by
            intro padRight hRightLayout
            exact ih rightSource hchildFail hrightLen n .cnf witness
              (.andRight
                (CircuitK1.evalCircuit
                  (CanonicalSATWitness.witnessAssignment witness) left) ::
                frames)
              (consumed + 3 + (encodeCircuit left).length)
              padRight hw hRightLayout
          have hout :=
            and_right_failure_step
              fuel n mode witness left rightSource frames
              consumed padding hw hLayout' hrec
          simpa [hsrc] using hout
      | orRight f rest left rightSource hleft hright =>
          have hsrc :
              rest = encodeCircuit left ++ rightSource :=
            decodeCircuitCore_success_sound
              fuel rest left rightSource hleft
          have hchildFail :
              RawDecodeFailure fuel rightSource :=
            rawDecodeFailure_of_none fuel rightSource hright
          have hrightLen : rightSource.length < fuel := by
            have henc := three_le_encodeCircuit_length left
            rw [hsrc] at hlen
            simp [List.length_append] at hlen
            omega
          have hLayout' :
              CheckedLayoutBound n consumed
                (true :: false :: true ::
                  (encodeCircuit left ++ rightSource))
                (encodeEvalFrames frames) := by
            simpa [hsrc] using hLayout
          have hrec :
              ∀ (padRight : Nat),
                CheckedLayoutBound n
                  (consumed + 3 + (encodeCircuit left).length)
                  rightSource
                  (encodeEvalFrames
                    (.orRight
                      (CircuitK1.evalCircuit
                        (CanonicalSATWitness.witnessAssignment witness)
                        left) :: frames)) →
                RawSinkCertificate fuel n .clause witness rightSource
                  (.orRight
                    (CircuitK1.evalCircuit
                      (CanonicalSATWitness.witnessAssignment witness)
                      left) :: frames)
                  (consumed + 3 + (encodeCircuit left).length)
                  padRight := by
            intro padRight hRightLayout
            exact ih rightSource hchildFail hrightLen n .clause witness
              (.orRight
                (CircuitK1.evalCircuit
                  (CanonicalSATWitness.witnessAssignment witness) left) ::
                frames)
              (consumed + 3 + (encodeCircuit left).length)
              padRight hw hRightLayout
          have hout :=
            or_right_failure_step
              fuel n mode witness left rightSource frames
              consumed padding hw hLayout' hrec
          simpa [hsrc] using hout

/-- Root specialization: any decodeCircuitCore failure at the whole-source fuel
reaches a physical evaluator failure sink under the root layout. -/
theorem root_core_none_reaches_sink
    (bits witness : BitString)
    (hw : witness.length = bits.length)
    (hcore :
      decodeCircuitCore (bits.length + 1) bits = none) :
    RawSinkCertificate (bits.length + 1) bits.length .cnf
      witness bits [] 0 0 := by
  have hfail :
      RawDecodeFailure (bits.length + 1) bits :=
    rawDecodeFailure_of_none (bits.length + 1) bits hcore
  exact rawDecodeFailure_reaches_sink
    (bits.length + 1) bits hfail (by omega)
    bits.length .cnf witness [] 0 0 hw
    (P01CheckedVerifierInvariant.root bits)

#print axioms MCore.Real.P01RawRecursiveClosure.rawDecodeFailure_reaches_sink
#print axioms MCore.Real.P01RawRecursiveClosure.root_core_none_reaches_sink

end P01RawRecursiveClosure
end Real
end MCore
