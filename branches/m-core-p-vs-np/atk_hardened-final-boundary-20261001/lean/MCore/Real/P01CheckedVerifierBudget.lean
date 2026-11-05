import MCore.Real.P01EvalStepSemanticRefinement
import MCore.Real.P01InputNodeCompositeRun
import MCore.Real.P01EncodedStackEvaluator
import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.P01CheckedEvalRunNeedTags
import MCore.Real.P01CheckedEvalRunInputTag

namespace MCore
namespace Real
namespace P01CheckedVerifierBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01NeedExprCompositeRun
open P01InputNodeCompositeRun
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunInputTag

/-- Exact unary length of the canonical natural-number payload. -/
theorem encodeNat_length (i : Nat) :
    (encodeNat i).length = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [encodeNat, ih, Nat.succ_eq_add_one]

/-- Uniform physical cost of one semantic evaluator transition when every
dynamic tape component is bounded by the original source length. -/
def checkedCoreEnvelope (n : Nat) : Nat :=
  64 * (n + 1) ^ 2

def checkedStepEnvelope (n : Nat) : Nat :=
  128 * (n + 1) ^ 2

theorem checkedStepEnvelope_poly :
    PolynomialTimeBound checkedStepEnvelope := by
  refine ⟨128, 2, ?_⟩
  intro n
  exact Nat.le_refl _

theorem constTagCompositeFuel_le_envelope
    (n : Nat) (frameStack rest : BitString)
    (hf : frameStack.length ≤ n)
    (hr : rest.length ≤ n) :
    constTagCompositeFuel frameStack rest ≤ checkedStepEnvelope n := by
  unfold constTagCompositeFuel checkedStepEnvelope
  have hlin :
      2 * frameStack.length + 2 * rest.length + 14 ≤ 4 * n + 14 := by
    omega
  have hlin' : 4 * n + 14 ≤ 18 * (n + 1) := by
    omega
  have hmul :
      18 * (n + 1) ≤ 18 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 18 (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hcoef :
      18 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simp [Nat.pow_two] at *
  omega

theorem pushTagCompositeFuel_le_envelope
    (n : Nat) (frameStack rest : BitString)
    (hf : frameStack.length ≤ n)
    (hr : rest.length ≤ n) :
    pushTagCompositeFuel frameStack rest ≤ checkedStepEnvelope n := by
  unfold pushTagCompositeFuel checkedStepEnvelope
  have hlin :
      2 * frameStack.length + 2 * rest.length + 18 ≤ 4 * n + 18 := by
    omega
  have hlin' : 4 * n + 18 ≤ 22 * (n + 1) := by
    omega
  have hmul :
      22 * (n + 1) ≤ 22 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 22 (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hcoef :
      22 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simp [Nat.pow_two] at *
  omega

/-- The complete 000 input primitive is also uniformly quadratic. -/
theorem inputNodeCompositeFuel_le_envelope
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (hc : consumed ≤ n)
    (hi : i ≤ n)
    (ht : tail.length ≤ n)
    (hf : frameStack.length ≤ n) :
    inputNodeCompositeFuel consumed i tail frameStack ≤
      checkedCoreEnvelope n := by
  have hbase :=
    inputNodeCompositeFuel_le consumed i tail frameStack
  have hcoef :
      2 * consumed + 4 * (i + 1) + 6 ≤ 6 * n + 10 := by
    omega
  have hmul :
      (2 * consumed + 4 * (i + 1) + 6) * i ≤
        (6 * n + 10) * n :=
    Nat.mul_le_mul hcoef hi
  have hrest :
      4 * consumed + 8 * i + tail.length + frameStack.length + 30 ≤
        14 * n + 30 := by
    omega
  have hcoef16 : 6 * n + 10 ≤ 16 * (n + 1) := by
    omega
  have hprod1 :
      (6 * n + 10) * n ≤ (16 * (n + 1)) * n :=
    Nat.mul_le_mul_right n hcoef16
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hprod2 :
      (16 * (n + 1)) * n ≤
        16 * ((n + 1) * (n + 1)) := by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left (16 * (n + 1)) hn
  have hrest30 : 14 * n + 30 ≤ 30 * (n + 1) := by
    omega
  have hrest2 :
      30 * (n + 1) ≤ 30 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 30
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hsum :
      (6 * n + 10) * n + (14 * n + 30) ≤
        46 * ((n + 1) * (n + 1)) := by
    omega
  have hcoef64 :
      46 * ((n + 1) * (n + 1)) ≤
        64 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  unfold checkedCoreEnvelope
  simp [Nat.pow_two]
  omega

theorem inputTagCompositeFuel_le_envelope
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (hc3 : consumed + 3 ≤ n)
    (hi : i ≤ n)
    (ht : tail.length ≤ n)
    (hf : frameStack.length ≤ n) :
    inputTagCompositeFuel consumed i tail frameStack ≤
      checkedStepEnvelope n := by
  have hnode :=
    inputNodeCompositeFuel_le_envelope
      n (consumed + 3) i tail frameStack
      hc3 hi ht hf
  have henc : (encodeNat i).length = i + 1 :=
    encodeNat_length i
  unfold inputTagCompositeFuel checkedStepEnvelope checkedCoreEnvelope at *
  have hpref :
      frameStack.length +
          (false :: false :: false :: (encodeNat i ++ tail)).length + 3 +
          1 + 3 + 1 ≤
        3 * n + 12 := by
    rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_append, henc]
    omega
  have hlin12 : 3 * n + 12 ≤ 12 * (n + 1) := by
    omega
  have hquad12 :
      12 * (n + 1) ≤ 12 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 12
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hsum :
      3 * n + 12 + 64 * ((n + 1) * (n + 1)) ≤
        76 * ((n + 1) * (n + 1)) := by
    omega
  have hcoef128 :
      76 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simp [Nat.pow_two] at *
  omega

/-- The checked syntax-mode tag prefix is uniformly quadratic (in fact
linear) in the original source bound. -/
theorem checkedTagPrefixFuel_le_envelope
    (n : Nat) (source frameStack : BitString)
    (hs : source.length ≤ n)
    (hf : frameStack.length ≤ n) :
    checkedTagPrefixFuel source frameStack ≤ checkedStepEnvelope n := by
  unfold checkedTagPrefixFuel checkedStepEnvelope
  have hlin :
      frameStack.length + source.length + 3 + 1 + 3 + 1 ≤
        2 * n + 8 := by
    omega
  have hlin' : 2 * n + 8 ≤ 10 * (n + 1) := by
    omega
  have hmul :
      10 * (n + 1) ≤ 10 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 10
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hcoef :
      10 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simp [Nat.pow_two]
  omega

/-- The checked continuation-producing tags remain under the same quadratic
envelope. -/
theorem checkedPushTagFuel_le_envelope
    (n : Nat) (source frameStack : BitString)
    (hs : source.length ≤ n)
    (hf : frameStack.length ≤ n) :
    checkedPushTagFuel source frameStack ≤ checkedStepEnvelope n := by
  have hdrop : (source.drop 3).length ≤ source.length := by
    simp
  unfold checkedPushTagFuel checkedTagPrefixFuel checkedStepEnvelope
  have hlin :
      frameStack.length + source.length + 3 + 1 + 3 + 1 +
          (source.drop 3).length + frameStack.length + 2 + 1 + 3 + 1
        ≤ 4 * n + 15 := by
    omega
  have hlin' : 4 * n + 15 ≤ 19 * (n + 1) := by
    omega
  have hmul :
      19 * (n + 1) ≤ 19 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 19
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hcoef :
      19 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simp [Nat.pow_two]
  omega

/-- Checked 000 input route: checked tag prefix plus the already-bounded fused
input-node primitive. -/
theorem checkedInputTagFuel_le
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (hsource :
      (false :: false :: false :: (encodeNat i ++ tail)).length ≤ n)
    (hc3 : consumed + 3 ≤ n)
    (hi : i ≤ n)
    (ht : tail.length ≤ n)
    (hf : frameStack.length ≤ n) :
    checkedInputTagFuel consumed i tail frameStack ≤
      256 * (n + 1) ^ 2 := by
  let source := false :: false :: false :: (encodeNat i ++ tail)
  have hp :
      checkedTagPrefixFuel source frameStack ≤ checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope n source frameStack
      (by simpa [source] using hsource) hf
  have hn :
      inputNodeCompositeFuel (consumed + 3) i tail frameStack ≤
        checkedCoreEnvelope n :=
    inputNodeCompositeFuel_le_envelope
      n (consumed + 3) i tail frameStack hc3 hi ht hf
  unfold checkedInputTagFuel checkedStepEnvelope checkedCoreEnvelope at *
  have hsum :
      checkedTagPrefixFuel source frameStack +
          inputNodeCompositeFuel (consumed + 3) i tail frameStack
        ≤ 192 * ((n + 1) * (n + 1)) := by
    simp [Nat.pow_two] at hp hn
    omega
  have hcoef :
      192 * ((n + 1) * (n + 1)) ≤
        256 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simpa [source, Nat.pow_two] using Nat.le_trans hsum hcoef

/-- Global candidate budget for the checked physical verifier.  The cubic
degree is enough for a linear number of semantic steps, each under a quadratic
physical envelope. -/
def checkedVerifierTimeBound : TimeBound :=
  fun n => 256 * (n + 1) ^ 3

theorem checkedVerifierTimeBound_poly :
    PolynomialTimeBound checkedVerifierTimeBound := by
  refine ⟨256, 3, ?_⟩
  intro n
  exact Nat.le_refl _

#print axioms MCore.Real.P01CheckedVerifierBudget.encodeNat_length
#print axioms MCore.Real.P01CheckedVerifierBudget.constTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.pushTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.inputNodeCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.inputTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.checkedTagPrefixFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.checkedPushTagFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.checkedInputTagFuel_le
#print axioms MCore.Real.P01CheckedVerifierBudget.checkedVerifierTimeBound_poly

end P01CheckedVerifierBudget
end Real
end MCore
