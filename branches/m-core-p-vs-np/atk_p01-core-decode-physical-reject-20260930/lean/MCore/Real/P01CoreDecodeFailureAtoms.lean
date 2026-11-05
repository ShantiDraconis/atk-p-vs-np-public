import MCore.Real.P01CheckedEvalRejectBounded
import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.P01MaterialGlobalBudget

namespace MCore
namespace Real
namespace P01CoreDecodeFailureAtoms

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunInputTag
open P01CheckedEvalRejectBounded
open P01CheckedVerifierGlobalBudget
open P01MaterialGlobalBudget

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Functional unary decoder failure means exactly that no false terminator
occurs: the whole residual source is a block of true bits. -/
theorem decodeNat_none_eq_replicate_true :
    ∀ bits : BitString,
      decodeNat bits = none →
      bits = List.replicate bits.length true
  | [], _ => by simp
  | false :: rest, h => by
      simp [decodeNat] at h
  | true :: rest, h => by
      simp only [decodeNat] at h
      cases hr : decodeNat rest with
      | some p =>
          simp [hr] at h
      | none =>
          have ih := decodeNat_none_eq_replicate_true rest hr
          simp [ih, List.replicate_succ]

/-- The checked-loop envelope is always below the material global envelope. -/
theorem checkedLoopStepEnvelope_le_material
    (n : Nat) :
    checkedLoopStepEnvelope n ≤ materialVerifierGlobalTimeBound n := by
  unfold checkedLoopStepEnvelope materialVerifierGlobalTimeBound
  have hpow : (n + 1)^2 ≤ (n + 1)^3 := by
    rw [Nat.pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hscale :
      256 * (n + 1)^2 ≤ 256 * (n + 1)^3 :=
    Nat.mul_le_mul_left 256 hpow
  exact Nat.le_trans hscale
    (Nat.mul_le_mul_right ((n + 1)^3) (by omega))

/-- Short raw sources (<3 bits) reject physically inside the material bound. -/
theorem short_source_rejects_material
    (n : Nat)
    (mode : SyntaxMode)
    (witness source frameStack : BitString)
    (consumed padding : Nat)
    (hshort : source.length < 3)
    (hsource : source.length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ materialVerifierGlobalTimeBound n,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   source frameStack padding }] := by
  obtain ⟨m, hm, tape, hrun⟩ :=
    short_tag_reaches_reject_within_envelope
      n mode witness source frameStack consumed padding
      hshort hsource hframes
  exact ⟨m, Nat.le_trans hm (checkedLoopStepEnvelope_le_material n),
    tape, hrun⟩

/-- Either invalid three-bit root tag (110 or 111) rejects physically in every
syntax mode, inside the material bound. -/
theorem invalid_tag_rejects_material
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (third : Bool)
    (hsource : (true :: true :: third :: rest).length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ materialVerifierGlobalTimeBound n,
      ({ state := .reject,
         tape := evalCursorReadTape witness (consumed + 3)
           rest frameStack padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: true :: third :: rest) frameStack padding }] := by
  have hdis :
      tagAllowed mode
        (P01NeedExprTagDecode.decodeTagBits true true third) = false := by
    cases mode <;> cases third <;> rfl
  obtain ⟨m, hm, hrun⟩ :=
    disallowed_tag_prefix_reaches_reject_within_envelope
      n mode witness rest frameStack consumed padding
      true true third hdis hsource hframes
  exact ⟨m, Nat.le_trans hm (checkedLoopStepEnvelope_le_material n), hrun⟩

/-- A 000 input tag whose unary index has no false terminator rejects
physically.  The source and frame-size hypotheses are the only accounting
inputs. -/
theorem unterminated_input_rejects_material
    (N : Nat)
    (mode : SyntaxMode)
    (witness frameStack : BitString)
    (consumed padding k : Nat)
    (hk : k ≤ N)
    (hframes : frameStack.length ≤ N) :
    ∃ m ≤ materialVerifierGlobalTimeBound N,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (false :: false :: false ::
                     List.replicate k true)
                   frameStack padding }] := by
  obtain ⟨m, hm, tape, hrun⟩ :=
    inputTag_unterminated_reaches_reject
      mode witness frameStack consumed padding k
  have hfuel :
      checkedUnterminatedInputFuel k frameStack ≤
        3 * N + 13 := by
    unfold checkedUnterminatedInputFuel checkedTagPrefixFuel
    simp
    omega
  have hbase : N + 1 ≤ (N + 1)^2 := by
    have hp : 1 ≤ N + 1 := by omega
    calc
      N + 1 = (N + 1) * 1 := by simp
      _ ≤ (N + 1) * (N + 1) :=
        Nat.mul_le_mul_left (N + 1) hp
      _ = (N + 1)^2 := by simp [Nat.pow_two]
  have hlinear : 3 * N + 13 ≤ 16 * (N + 1) := by omega
  have hscale :
      16 * (N + 1) ≤ 16 * (N + 1)^2 :=
    Nat.mul_le_mul_left 16 hbase
  have hlin :
      3 * N + 13 ≤ 16 * (N + 1)^2 :=
    Nat.le_trans hlinear hscale
  have htoLoop :
      16 * (N + 1)^2 ≤ checkedLoopStepEnvelope N := by
    unfold checkedLoopStepEnvelope
    exact Nat.mul_le_mul_right ((N + 1)^2) (by omega)
  have hmat :=
    checkedLoopStepEnvelope_le_material N
  exact ⟨m,
    Nat.le_trans hm
      (Nat.le_trans hfuel
        (Nat.le_trans hlin
          (Nat.le_trans htoLoop hmat))),
    tape, hrun⟩

/-- Root-level 000 decoder failure is therefore physically closed. -/
theorem input_decode_failure_rejects_material
    (N : Nat)
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (hdecode : decodeNat rest = none)
    (hrest : rest.length ≤ N)
    (hframes : frameStack.length ≤ N) :
    ∃ m ≤ materialVerifierGlobalTimeBound N,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (false :: false :: false :: rest)
                   frameStack padding }] := by
  have hrep := decodeNat_none_eq_replicate_true rest hdecode
  have hbase :=
    unterminated_input_rejects_material
      N mode witness frameStack consumed padding rest.length
      hrest hframes
  simpa [hrep] using hbase

#print axioms MCore.Real.P01CoreDecodeFailureAtoms.decodeNat_none_eq_replicate_true
#print axioms MCore.Real.P01CoreDecodeFailureAtoms.short_source_rejects_material
#print axioms MCore.Real.P01CoreDecodeFailureAtoms.invalid_tag_rejects_material
#print axioms MCore.Real.P01CoreDecodeFailureAtoms.unterminated_input_rejects_material

end P01CoreDecodeFailureAtoms
end Real
end MCore
