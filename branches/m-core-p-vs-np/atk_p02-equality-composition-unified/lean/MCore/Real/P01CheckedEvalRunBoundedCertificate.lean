import MCore.Real.P01CheckedEvalRunBoundedInput
import MCore.Real.P01CheckedEvalRunBoundedConst
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01CheckedVerifierInvariant
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunInputTag
open P01CheckedEvalRunBoundedInput
open P01CheckedEvalRunBoundedConst
open P01CheckedEvalRunBoundedHelpers
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Deliberately loose structural budget for a whole checked circuit run.

The factor 8 absorbs the finite physical wrapper work around every semantic
evaluator transition.  It is still linear in evalStepCount and therefore
cubic after multiplication by the quadratic checked-loop envelope. -/
def checkedCircuitBudget
    (phi : CircuitK1.Circuit) (n : Nat) : Nat :=
  8 * (evalStepCount phi + 1) * checkedLoopStepEnvelope n

theorem loopEnvelope_le_checkedCircuitBudget
    (phi : CircuitK1.Circuit) (n : Nat) :
    checkedLoopStepEnvelope n ≤ checkedCircuitBudget phi n := by
  unfold checkedCircuitBudget
  have hfactor : 1 ≤ 8 * (evalStepCount phi + 1) := by
    omega
  calc
    checkedLoopStepEnvelope n
        = 1 * checkedLoopStepEnvelope n := by simp
    _ ≤ (8 * (evalStepCount phi + 1)) * checkedLoopStepEnvelope n :=
      Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hfactor

/-- Bounded analogue of CheckedCircuitRunCertificate.

The layout invariant is an explicit premise: it is exactly what lets every
local physical producer inherit the same source-length parameter n. -/
def BoundedCheckedCircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : CircuitK1.Circuit) : Prop :=
  modeCheck mode phi = true →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
    CheckedLayoutBound n consumed
      (encodeCircuit phi ++ tail) (encodeEvalFrames frames) →
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m ≤ checkedCircuitBudget phi n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness (exitMode mode phi)
        (evalCircuit sigma phi) tail frames cfg

/-- Input leaf: the already-bounded checked 000 producer inhabits the bounded
circuit certificate. -/
theorem input_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    BoundedCheckedCircuitRunCertificate sigma witness mode (.input i) := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar

  have hLayoutInput :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_within_loopEnvelope
      n mode witness tail (encodeEvalFrames frames)
      consumed padding i hi hLayoutInput

  let cfg : CheckedConfig :=
    inputCheckedConfig mode
      ({ state :=
           .done (witness.getD i false)
             (P01InputNodeCompositeRun.inputNodeFinalMode
               tail (encodeEvalFrames frames)),
         tape :=
           (P01InputNodeRoundTrip.inputAfterReadTarget witness
             (P01InputNodeRoundTrip.consumedAfterInputIndex
               (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
          (Option Bool))

  refine ⟨m,
    Nat.le_trans hm (loopEnvelope_le_checkedCircuitBudget (.input i) n),
    cfg, ?_, ?_⟩
  · simpa [cfg, encodeCircuit] using hrun
  · change CheckedLoopOutcome witness (exitMode mode (.input i))
      (sigma i) tail frames cfg
    rw [← hvalue]
    cases tail with
    | cons b bs =>
        refine ⟨P01InputNodeRoundTrip.consumedAfterInputIndex
          (consumed + 3) i, padding, ?_⟩
        simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
          cfg, inputCheckedConfig, inputCheckedEmbed,
          P01InputNodeCompositeRun.inputNodeFinalMode,
          P01InputNodeRoundTrip.inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(P01InputNodeRoundTrip.inputAfterReadTarget witness
              (P01InputNodeRoundTrip.consumedAfterInputIndex
                (consumed + 3) i)
              [] [] padding).tape, ?_⟩
            simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
              cfg, inputCheckedConfig, inputCheckedEmbed,
              P01InputNodeCompositeRun.inputNodeFinalMode,
              P01InputNodeRoundTrip.inputAfterReadTarget]
        | cons f fs =>
            refine ⟨P01InputNodeRoundTrip.consumedAfterInputIndex
              (consumed + 3) i, padding, ?_⟩
            cases f with
            | neg =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  P01InputNodeRoundTrip.inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andLeft =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  P01InputNodeRoundTrip.inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andRight a =>
                cases a <;> simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  P01InputNodeRoundTrip.inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | orLeft =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  P01InputNodeRoundTrip.inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | orRight a =>
                cases a <;> simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  P01InputNodeRoundTrip.inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]

/-- Constant leaf: the generic bounded constant run inhabits the same bounded
circuit certificate. -/
theorem const_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    BoundedCheckedCircuitRunCertificate sigma witness mode (.const v) := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  obtain ⟨m, hm, cfg, hrun, hout⟩ :=
    const_checked_run_within_loopEnvelope
      n sigma witness tail frames mode consumed padding v hmode hLayout
  refine ⟨m,
    Nat.le_trans hm (loopEnvelope_le_checkedCircuitBudget (.const v) n),
    cfg, hrun, ?_⟩
  simpa [evalCircuit] using hout

#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.loopEnvelope_le_checkedCircuitBudget
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.input_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.const_bounded_certificate

end P01CheckedEvalRunBoundedCertificate
end Real
end MCore
