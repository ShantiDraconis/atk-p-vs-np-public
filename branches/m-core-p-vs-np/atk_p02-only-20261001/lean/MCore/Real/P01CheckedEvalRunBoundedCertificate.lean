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
open P01NTMRunLaws

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
                cases a <;>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
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
                cases a <;>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
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


/-- Negation: compose one bounded tag transition, the bounded child,
the bounded continuation return, and final outcome normalization. -/
theorem neg_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : CircuitK1.Circuit)
    (hchild :
      BoundedCheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) child) :
    BoundedCheckedCircuitRunCertificate sigma witness mode (.not child) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      tagAllowed mode .neg = true ∧
        modeCheck (childMode mode .neg) child = true := by
    have h := hmode
    rw [modeCheck_not] at h
    simpa using h
  have hAllowed := hparts.1
  have hchildMode := hparts.2

  have hlenChild : varBound child ≤ witness.length := by
    simpa [varBound] using hlen
  have hreadChild :
      ∀ i, i < varBound child →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by simpa [varBound] using hi)

  have hLayout0 :
      CheckedLayoutBound n consumed
        (false :: true :: true :: (encodeCircuit child ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  have hLayoutChild :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit child ++ tail)
        (encodeEvalFrame .neg ++ encodeEvalFrames frames) :=
    after_push_tag n consumed false true true
      (encodeCircuit child ++ tail) (encodeEvalFrames frames) .neg hLayout0

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness (encodeCircuit child ++ tail)
      (encodeEvalFrames frames) consumed padding
      false true true .neg .neg rfl hAllowed rfl
      hLayout0.source_le hLayout0.frames_le

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : CheckedConfig :=
    { state := .need (childMode mode .neg)
        needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit child ++ tail)
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutChild)
      hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not child) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  simp [CheckedLoopOutcome] at hout1
  rcases hout1 with ⟨consumed1, padding1, hcfg1⟩
  subst cfg1

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_checked_reaches_have_within_envelope
      n (exitMode (childMode mode .neg) child)
      witness tail (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma child)

  let cHave : CheckedConfig :=
    { state := .have (exitMode (childMode mode .neg) child)
        (.start (!(evalCircuit sigma child))),
      tape :=
        evalCursorStackEndTape witness consumed1 tail
          (encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have (exitMode (childMode mode .neg) child)
               (.start (evalCircuit sigma child)),
             tape :=
               evalCursorStackEndTape witness consumed1 tail
                 (encodeEvalFrame .neg ++ encodeEvalFrames frames)
                 padding1 }] := by
    simpa [cHave] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not child) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode (childMode mode .neg) child)
           (.start (evalCircuit sigma child)),
         tape :=
           evalCursorStackEndTape witness consumed1 tail
             (encodeEvalFrame .neg ++ encodeEvalFrames frames)
             padding1 } : CheckedConfig)
      cHave h01 h2'

  obtain ⟨m3, hm3, cfgFinal, h3, hout3⟩ :=
    have_reaches_outcome_within_envelope
      n (exitMode (childMode mode .neg) child)
      witness (!(evalCircuit sigma child))
      tail frames consumed1 (padding1 + 3)

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not child) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h012 h3

  have hbudget :
      checkedLoopStepEnvelope n +
          checkedCircuitBudget child n +
          checkedLoopStepEnvelope n +
          checkedLoopStepEnvelope n ≤
        checkedCircuitBudget (.not child) n := by
    let E := checkedLoopStepEnvelope n
    have hpack :
        checkedCircuitBudget child n + 3 * E =
          (8 * (evalStepCount child + 1) + 3) * E := by
      unfold checkedCircuitBudget
      dsimp [E]
      rw [Nat.add_mul]
    have hcoef :
        8 * (evalStepCount child + 1) + 3 ≤
          8 * (evalStepCount child + 3) := by
      omega
    have hmul :
        (8 * (evalStepCount child + 1) + 3) * E ≤
          (8 * (evalStepCount child + 3)) * E :=
      Nat.mul_le_mul_right E hcoef
    have hcount :
        evalStepCount (.not child) + 1 =
          evalStepCount child + 3 := by
      simp [evalStepCount]
      omega
    calc
      checkedLoopStepEnvelope n +
            checkedCircuitBudget child n +
            checkedLoopStepEnvelope n +
            checkedLoopStepEnvelope n
          = checkedCircuitBudget child n + 3 * E := by
              dsimp [E]
              omega
      _ = (8 * (evalStepCount child + 1) + 3) * E := hpack
      _ ≤ (8 * (evalStepCount child + 3)) * E := hmul
      _ = checkedCircuitBudget (.not child) n := by
            unfold checkedCircuitBudget
            rw [hcount]

  have hchildInput :
      ∃ i, child = .input i := by
    have hm : modeCheck .mustInput child = true := by
      simpa [childMode] using hchildMode
    exact (modeCheck_mustInput_iff child).1 hm
  have hExit :
      exitMode (childMode mode .neg) child =
        exitMode mode (.not child) := by
    rcases hchildInput with ⟨i, rfl⟩
    simp [exitMode, childMode, circuitTag]

  refine ⟨m0 + m1 + m2 + m3, ?_, cfgFinal, hAll, ?_⟩
  · exact Nat.le_trans (by omega) hbudget
  · rw [← hExit]
    simpa [evalCircuit] using hout3

#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.loopEnvelope_le_checkedCircuitBudget
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.input_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.const_bounded_certificate

end P01CheckedEvalRunBoundedCertificate
end Real
end MCore
