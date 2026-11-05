import MCore.Real.P01RawRecursiveSteps
import MCore.Real.P01RawDecodeFailureShape
import MCore.Real.P01RawDecoderSound

namespace MCore
namespace Real
namespace P01RawDecodeInduction

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01CheckedVerifierInvariant
open P01RawEvalSink
open P01RawRecursiveBudget
open P01RawRecursiveSteps
open P01RawDecoderSound

/-- Physical completeness of raw decoder failure.

The proof follows decodeCircuitCore by fuel.  The static invariant
bits.length < fuel is exactly what holds at the whole-source call
fuel = bits.length + 1, and it is preserved by every recursive decoder call.
-/
theorem decodeCore_none_reaches_sink :
    ∀ (fuel : Nat) (bits : BitString),
      bits.length < fuel →
      decodeCircuitCore fuel bits = none →
      ∀ (mode : SyntaxMode)
          (witness : BitString)
          (frames : List EvalFrame)
          (consumed padding n : Nat),
        witness.length = n →
        CheckedLayoutBound n consumed bits
          (encodeEvalFrames frames) →
        RawSinkCertificate fuel n mode witness bits
          frames consumed padding := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits hlen
      omega
  | succ fuel ih =>
      intro bits hlen hdec mode witness frames consumed padding n hw hLayout
      cases bits with
      | nil =>
          have hlocal :=
            truncated_tag_reaches_sink
              n mode witness [] frames consumed padding
              (by simp) hLayout
          simpa [Nat.succ_eq_add_one] using
            (chunk_sink_to_succ fuel n mode witness [] frames
              consumed padding hlocal)
      | cons b0 tail0 =>
          cases tail0 with
          | nil =>
              have hlocal :=
                truncated_tag_reaches_sink
                  n mode witness [b0] frames consumed padding
                  (by simp) hLayout
              simpa [Nat.succ_eq_add_one] using
                (chunk_sink_to_succ fuel n mode witness [b0] frames
                  consumed padding hlocal)
          | cons b1 tail1 =>
              cases tail1 with
              | nil =>
                  have hlocal :=
                    truncated_tag_reaches_sink
                      n mode witness [b0, b1] frames consumed padding
                      (by simp) hLayout
                  simpa [Nat.succ_eq_add_one] using
                    (chunk_sink_to_succ fuel n mode witness [b0, b1] frames
                      consumed padding hlocal)
              | cons b2 rest =>
                  cases b0 with
                  | false =>
                      cases b1 with
                      | false =>
                          cases b2 with
                          | false =>
                              -- 000: decoder failure is exactly unary-index exhaustion.
                              cases hn : decodeNat rest with
                              | none =>
                                  have hlocal :=
                                    unary_none_reaches_sink
                                      n mode witness rest frames
                                      consumed padding (by simpa using hn)
                                      hLayout
                                  simpa [Nat.succ_eq_add_one] using
                                    (chunk_sink_to_succ fuel n mode witness
                                      (false :: false :: false :: rest)
                                      frames consumed padding hlocal)
                              | some p =>
                                  simp [decodeCircuitCore, hn] at hdec
                          | true =>
                              -- 001 const-false always structurally decodes.
                              simp [decodeCircuitCore] at hdec
                      | true =>
                          cases b2 with
                          | false =>
                              -- 010 const-true always structurally decodes.
                              simp [decodeCircuitCore] at hdec
                          | true =>
                              -- 011 NOT: recurse on the unique child when its decoder fails.
                              cases hc : decodeCircuitCore fuel rest with
                              | none =>
                                  have hrestLen : rest.length < fuel := by
                                    simp at hlen
                                    omega
                                  have hChildLayout :
                                      CheckedLayoutBound n (consumed + 3) rest
                                        (encodeEvalFrames (.neg :: frames)) := by
                                    have h :=
                                      P01CheckedVerifierInvariant.after_push_tag
                                        n consumed false true true rest
                                        (encodeEvalFrames frames) .neg hLayout
                                    simpa [encodeEvalFrames, List.append_assoc] using h
                                  have hrec :
                                      RawSinkCertificate fuel n
                                        (childMode mode .neg)
                                        witness rest (.neg :: frames)
                                        (consumed + 3)
                                        (((padding - 1) - 1) - 1) :=
                                    ih rest hrestLen (by simpa using hc)
                                      (childMode mode .neg)
                                      witness (.neg :: frames)
                                      (consumed + 3)
                                      (((padding - 1) - 1) - 1)
                                      n hw hChildLayout
                                  simpa [Nat.succ_eq_add_one] using
                                    (not_child_failure_step
                                      fuel n mode witness rest frames
                                      consumed padding hLayout hrec)
                              | some p =>
                                  simp [decodeCircuitCore, hc] at hdec
                  | true =>
                      cases b1 with
                      | false =>
                          cases b2 with
                          | false =>
                              -- 100 AND.
                              cases hl : decodeCircuitCore fuel rest with
                              | none =>
                                  have hrestLen : rest.length < fuel := by
                                    simp at hlen
                                    omega
                                  have hChildLayout :
                                      CheckedLayoutBound n (consumed + 3) rest
                                        (encodeEvalFrames (.andLeft :: frames)) := by
                                    have h :=
                                      P01CheckedVerifierInvariant.after_push_tag
                                        n consumed true false false rest
                                        (encodeEvalFrames frames) .andLeft hLayout
                                    simpa [encodeEvalFrames, List.append_assoc] using h
                                  have hrec :
                                      RawSinkCertificate fuel n .cnf
                                        witness rest (.andLeft :: frames)
                                        (consumed + 3)
                                        (((padding - 1) - 1) - 1) :=
                                    ih rest hrestLen (by simpa using hl)
                                      .cnf witness (.andLeft :: frames)
                                      (consumed + 3)
                                      (((padding - 1) - 1) - 1)
                                      n hw hChildLayout
                                  simpa [Nat.succ_eq_add_one] using
                                    (and_left_failure_step
                                      fuel n mode witness rest frames
                                      consumed padding hLayout hrec)
                              | some p =>
                                  rcases p with ⟨left, rightSource⟩
                                  cases hr :
                                      decodeCircuitCore fuel rightSource with
                                  | none =>
                                      have hrestEq :
                                          rest =
                                            encodeCircuit left ++ rightSource :=
                                        P01RawDecoderSound.decodeCircuitCore_success_sound
                                          fuel rest left rightSource
                                          (by simpa using hl)
                                      have hrightLen :
                                          rightSource.length < fuel := by
                                        have hs : rightSource.length ≤ rest.length := by
                                          rw [hrestEq]
                                          simp
                                        simp at hlen
                                        omega
                                      have hLayout' :
                                          CheckedLayoutBound n consumed
                                            (true :: false :: false ::
                                              (encodeCircuit left ++ rightSource))
                                            (encodeEvalFrames frames) := by
                                        simpa [hrestEq] using hLayout
                                      have hrecRight :
                                          ∀ (padRight : Nat),
                                            CheckedLayoutBound n
                                              (consumed + 3 +
                                                (encodeCircuit left).length)
                                              rightSource
                                              (encodeEvalFrames
                                                (.andRight
                                                  (evalCircuit
                                                    (P01RawRecursiveSteps.witnessAssignment witness)
                                                    left) :: frames)) →
                                            RawSinkCertificate fuel n .cnf
                                              witness rightSource
                                              (.andRight
                                                (evalCircuit
                                                  (P01RawRecursiveSteps.witnessAssignment witness)
                                                  left) :: frames)
                                              (consumed + 3 +
                                                (encodeCircuit left).length)
                                              padRight := by
                                        intro padRight hRightLayout
                                        exact ih rightSource hrightLen
                                          (by simpa using hr)
                                          .cnf witness
                                          (.andRight
                                            (evalCircuit
                                              (P01RawRecursiveSteps.witnessAssignment witness)
                                              left) :: frames)
                                          (consumed + 3 +
                                            (encodeCircuit left).length)
                                          padRight n hw hRightLayout
                                      simpa [Nat.succ_eq_add_one, hrestEq] using
                                        (and_right_failure_step
                                          fuel n mode witness left rightSource
                                          frames consumed padding hw hLayout'
                                          hrecRight)
                                  | some q =>
                                      simp [decodeCircuitCore, hl, hr] at hdec
                          | true =>
                              -- 101 OR.
                              cases hl : decodeCircuitCore fuel rest with
                              | none =>
                                  have hrestLen : rest.length < fuel := by
                                    simp at hlen
                                    omega
                                  have hChildLayout :
                                      CheckedLayoutBound n (consumed + 3) rest
                                        (encodeEvalFrames (.orLeft :: frames)) := by
                                    have h :=
                                      P01CheckedVerifierInvariant.after_push_tag
                                        n consumed true false true rest
                                        (encodeEvalFrames frames) .orLeft hLayout
                                    simpa [encodeEvalFrames, List.append_assoc] using h
                                  have hrec :
                                      RawSinkCertificate fuel n .clause
                                        witness rest (.orLeft :: frames)
                                        (consumed + 3)
                                        (((padding - 1) - 1) - 1) :=
                                    ih rest hrestLen (by simpa using hl)
                                      .clause witness (.orLeft :: frames)
                                      (consumed + 3)
                                      (((padding - 1) - 1) - 1)
                                      n hw hChildLayout
                                  simpa [Nat.succ_eq_add_one] using
                                    (or_left_failure_step
                                      fuel n mode witness rest frames
                                      consumed padding hLayout hrec)
                              | some p =>
                                  rcases p with ⟨left, rightSource⟩
                                  cases hr :
                                      decodeCircuitCore fuel rightSource with
                                  | none =>
                                      have hrestEq :
                                          rest =
                                            encodeCircuit left ++ rightSource :=
                                        P01RawDecoderSound.decodeCircuitCore_success_sound
                                          fuel rest left rightSource
                                          (by simpa using hl)
                                      have hrightLen :
                                          rightSource.length < fuel := by
                                        have hs : rightSource.length ≤ rest.length := by
                                          rw [hrestEq]
                                          simp
                                        simp at hlen
                                        omega
                                      have hLayout' :
                                          CheckedLayoutBound n consumed
                                            (true :: false :: true ::
                                              (encodeCircuit left ++ rightSource))
                                            (encodeEvalFrames frames) := by
                                        simpa [hrestEq] using hLayout
                                      have hrecRight :
                                          ∀ (padRight : Nat),
                                            CheckedLayoutBound n
                                              (consumed + 3 +
                                                (encodeCircuit left).length)
                                              rightSource
                                              (encodeEvalFrames
                                                (.orRight
                                                  (evalCircuit
                                                    (P01RawRecursiveSteps.witnessAssignment witness)
                                                    left) :: frames)) →
                                            RawSinkCertificate fuel n .clause
                                              witness rightSource
                                              (.orRight
                                                (evalCircuit
                                                  (P01RawRecursiveSteps.witnessAssignment witness)
                                                  left) :: frames)
                                              (consumed + 3 +
                                                (encodeCircuit left).length)
                                              padRight := by
                                        intro padRight hRightLayout
                                        exact ih rightSource hrightLen
                                          (by simpa using hr)
                                          .clause witness
                                          (.orRight
                                            (evalCircuit
                                              (P01RawRecursiveSteps.witnessAssignment witness)
                                              left) :: frames)
                                          (consumed + 3 +
                                            (encodeCircuit left).length)
                                          padRight n hw hRightLayout
                                      simpa [Nat.succ_eq_add_one, hrestEq] using
                                        (or_right_failure_step
                                          fuel n mode witness left rightSource
                                          frames consumed padding hw hLayout'
                                          hrecRight)
                                  | some q =>
                                      simp [decodeCircuitCore, hl, hr] at hdec
                      | true =>
                          cases b2 with
                          | false =>
                              -- 110 is structurally invalid in every syntax mode.
                              have hdis :
                                  tagAllowed mode
                                      (P01NeedExprTagDecode.decodeTagBits
                                        true true false) = false := by
                                cases mode <;> rfl
                              have hlocal :=
                                disallowed_tag_reaches_sink
                                  n mode witness rest frames consumed padding
                                  true true false hdis hLayout
                              simpa [Nat.succ_eq_add_one] using
                                (chunk_sink_to_succ fuel n mode witness
                                  (true :: true :: false :: rest)
                                  frames consumed padding hlocal)
                          | true =>
                              -- 111 is structurally invalid in every syntax mode.
                              have hdis :
                                  tagAllowed mode
                                      (P01NeedExprTagDecode.decodeTagBits
                                        true true true) = false := by
                                cases mode <;> rfl
                              have hlocal :=
                                disallowed_tag_reaches_sink
                                  n mode witness rest frames consumed padding
                                  true true true hdis hLayout
                              simpa [Nat.succ_eq_add_one] using
                                (chunk_sink_to_succ fuel n mode witness
                                  (true :: true :: true :: rest)
                                  frames consumed padding hlocal)

#print axioms MCore.Real.P01RawDecodeInduction.decodeCore_none_reaches_sink

end P01RawDecodeInduction
end Real
end MCore
