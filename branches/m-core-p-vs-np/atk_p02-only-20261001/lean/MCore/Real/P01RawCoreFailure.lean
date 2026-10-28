import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01RawMalformedTag
import MCore.Real.P01RawMalformedUnary
import MCore.Real.P01RawVerifierLift
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01GuessedWitnessRelation
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawCoreFailure

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01GuessedWitnessRelation
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode
open P01NTMRunLaws
open P01RawMalformedTag
open P01RawMalformedUnary

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Fail-closed endpoint of the checked evaluator.  Either the explicit reject
state was reached, or an active state has no successor. -/
def RawFailEndpoint (cfg : CheckedConfig) : Prop :=
  cfg.state = .reject ∨
    (¬ Halted checkedEvalRunLoopMachine cfg ∧
      checkedEvalRunLoopMachine.successors cfg = [])

/-- Loose compositional budget for a malformed raw prefix.  The factor 64
absorbs one checked-loop envelope per physical syntax event. -/
def rawCoreBudget (sourceLen n : Nat) : Nat :=
  64 * (sourceLen + 1) * checkedLoopStepEnvelope n

/-- Unary decoding fails exactly on a finite string of true markers. -/
theorem decodeNat_eq_none_eq_replicate_true :
    ∀ bits : BitString,
      decodeNat bits = none →
        bits = List.replicate bits.length true := by
  intro bits
  induction bits with
  | nil =>
      intro h
      rfl
  | cons b bs ih =>
      cases b with
      | false =>
          intro h
          simp [decodeNat] at h
      | true =>
          intro h
          simp only [decodeNat] at h
          cases hrest : decodeNat bs with
          | none =>
              have hrs : bs = List.replicate bs.length true :=
                ih hrest
              simp [hrs, List.replicate_succ]
          | some p =>
              simp [hrest] at h

theorem one_loop_le_rawCoreBudget
    (sourceLen n : Nat) :
    checkedLoopStepEnvelope n ≤ rawCoreBudget sourceLen n := by
  unfold rawCoreBudget
  have h : 1 ≤ 64 * (sourceLen + 1) := by omega
  exact Nat.le_trans
    (by simp)
    (Nat.mul_le_mul_right (checkedLoopStepEnvelope n) h)

theorem two_loop_le_rawCoreBudget
    (sourceLen n : Nat) :
    2 * checkedLoopStepEnvelope n ≤ rawCoreBudget sourceLen n := by
  unfold rawCoreBudget
  have h : 2 ≤ 64 * (sourceLen + 1) := by omega
  exact Nat.mul_le_mul_right (checkedLoopStepEnvelope n) h

/-- A short source already yields the generic active-dead endpoint. -/
theorem truncated_tag_reaches_raw_failure
    (n : Nat)
    (mode : SyntaxMode)
    (witness source : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hshort : source.length < 3)
    (hLayout :
      CheckedLayoutBound n consumed source (encodeEvalFrames frames)) :
    ∃ m ≤ rawCoreBudget source.length n, ∃ cfg : CheckedConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed source
               (encodeEvalFrames frames) padding }] ∧
      RawFailEndpoint cfg := by
  obtain ⟨m, hm, dead, hreach, hactive, hdead⟩ :=
    checked_truncated_tag_reaches_dead
      mode witness source (encodeEvalFrames frames)
      consumed padding hshort
  have hs : source.length ≤ n := hLayout.source_le
  have hf : (encodeEvalFrames frames).length ≤ n := hLayout.frames_le
  have hlinear :
      (encodeEvalFrames frames).length + source.length + 7 ≤
        checkedLoopStepEnvelope n := by
    unfold checkedLoopStepEnvelope
    have h1 : n + 1 ≤ (n + 1) * (n + 1) :=
      Nat.le_mul_of_pos_right (n + 1) (by omega)
    have hsmall :
        (encodeEvalFrames frames).length + source.length + 7 ≤
          9 * (n + 1) := by omega
    have hquad : 9 * (n + 1) ≤ 9 * ((n + 1) * (n + 1)) :=
      Nat.mul_le_mul_left 9 h1
    have hcoef :
        9 * ((n + 1) * (n + 1)) ≤
          256 * ((n + 1) * (n + 1)) :=
      Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
    simpa [Nat.pow_two] using
      Nat.le_trans hsmall (Nat.le_trans hquad hcoef)
  refine ⟨m,
    Nat.le_trans hm
      (Nat.le_trans hlinear (one_loop_le_rawCoreBudget source.length n)),
    dead, hreach, ?_⟩
  exact Or.inr ⟨hactive, hdead⟩

/-- A 000 tag whose unary index has no terminating false reaches the already
certified active-dead lookahead state. -/
theorem truncated_unary_reaches_raw_failure
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : decodeNat rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: rest) (encodeEvalFrames frames)) :
    ∃ m ≤ rawCoreBudget
          (false :: false :: false :: rest).length n,
      ∃ cfg : CheckedConfig,
        cfg ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: rest)
                 (encodeEvalFrames frames) padding }] ∧
        RawFailEndpoint cfg := by
  have hrep := decodeNat_eq_none_eq_replicate_true rest hrest
  let k := rest.length
  have hsource :
      (false :: false :: false :: List.replicate k true).length ≤ n := by
    simpa [k, hrep] using hLayout.source_le
  have hframes : (encodeEvalFrames frames).length ≤ n :=
    hLayout.frames_le
  obtain ⟨m, hm, dead, hreach, hactive, hdead⟩ :=
    checked_truncated_unary_reaches_dead
      mode witness (encodeEvalFrames frames) consumed padding k
  have htag :
      checkedTagPrefixFuel
          (false :: false :: false :: List.replicate k true)
          (encodeEvalFrames frames) ≤
        checkedStepEnvelope n := by
    exact checkedTagPrefixFuel_le_envelope
      n
      (false :: false :: false :: List.replicate k true)
      (encodeEvalFrames frames) hsource hframes
  have hk : k + 1 ≤ checkedLoopStepEnvelope n := by
    unfold checkedLoopStepEnvelope
    have hk0 : k ≤ n := by
      simpa [k] using
        Nat.le_trans (by simp : rest.length ≤ (false :: false :: false :: rest).length)
          hLayout.source_le
    have hsmall : k + 1 ≤ n + 1 := Nat.succ_le_succ hk0
    have h1 : n + 1 ≤ (n + 1) * (n + 1) :=
      Nat.le_mul_of_pos_right (n + 1) (by omega)
    have hcoef :
        (n + 1) * (n + 1) ≤
          256 * ((n + 1) * (n + 1)) := by
      nlinarith
    simpa [Nat.pow_two] using
      Nat.le_trans hsmall (Nat.le_trans h1 hcoef)
  have htag' :
      checkedTagPrefixFuel
          (false :: false :: false :: List.replicate k true)
          (encodeEvalFrames frames) ≤
        checkedLoopStepEnvelope n :=
    Nat.le_trans htag (checkedStepEnvelope_le_loopEnvelope n)
  have hm' : m ≤ 2 * checkedLoopStepEnvelope n := by
    omega
  refine ⟨m,
    Nat.le_trans hm'
      (two_loop_le_rawCoreBudget
        (false :: false :: false :: rest).length n),
    dead, ?_, ?_⟩
  · simpa [k, hrep] using hreach
  · exact Or.inr ⟨hactive, hdead⟩

/-- Any syntactically forbidden complete tag reaches the explicit reject
state within the raw budget. -/
theorem disallowed_tag_reaches_raw_failure
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdisallowed :
      tagAllowed mode (decodeTagBits b0 b1 b2) = false)
    (hLayout :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames)) :
    ∃ m ≤ rawCoreBudget (b0 :: b1 :: b2 :: rest).length n,
      ∃ cfg : CheckedConfig,
        cfg ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 (encodeEvalFrames frames) padding }] ∧
        RawFailEndpoint cfg := by
  obtain ⟨m, hm, hreach⟩ :=
    disallowed_tag_prefix_reaches_reject
      mode witness rest (encodeEvalFrames frames)
      consumed padding b0 b1 b2 hdisallowed
  have htag :
      checkedTagPrefixFuel (b0 :: b1 :: b2 :: rest)
          (encodeEvalFrames frames) ≤ checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope n
      (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames)
      hLayout.source_le hLayout.frames_le
  have hm' : m ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans hm
      (Nat.le_trans htag (checkedStepEnvelope_le_loopEnvelope n))
  let cfg : CheckedConfig :=
    { state := .reject,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          rest (encodeEvalFrames frames) padding }
  refine ⟨m,
    Nat.le_trans hm'
      (one_loop_le_rawCoreBudget
        (b0 :: b1 :: b2 :: rest).length n),
    cfg, ?_, ?_⟩
  · simpa [cfg] using hreach
  · exact Or.inl rfl

#print axioms MCore.Real.P01RawCoreFailure.decodeNat_eq_none_eq_replicate_true
#print axioms MCore.Real.P01RawCoreFailure.truncated_tag_reaches_raw_failure
#print axioms MCore.Real.P01RawCoreFailure.truncated_unary_reaches_raw_failure
#print axioms MCore.Real.P01RawCoreFailure.disallowed_tag_reaches_raw_failure

end P01RawCoreFailure
end Real
end MCore
