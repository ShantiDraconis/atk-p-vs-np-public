import MCore.Real.P01CheckedEvalRunBoundedInput
import MCore.Real.P01CheckedEvalRunBoundedConst
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01CheckedVerifierInvariant
import MCore.Real.P01CheckedVerifierGlobalBudget
import MCore.Real.P01CheckedEvalRunCircuitCertificate

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
open P01CheckedEvalRunCircuitCertificate
open P01CheckedEvalRunHaveValue
open P01NTMRunLaws
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
            | andRight b =>
                cases b <;> simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
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
            | orRight b =>
                cases b <;> simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
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


/-- Bounded structural producer for negation.

No new machine is introduced. The proof composes:
1. the checked three-bit negation prefix;
2. the bounded certificate for the literal child;
3. the certified negation frame return; and
4. the common checked outcome normalization.

The same CheckedLayoutBound is propagated through the child call, so every
physical subrun is charged to the original source-length parameter. -/
theorem neg_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (circuit : CircuitK1.Circuit)
    (hchild :
      BoundedCheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) circuit) :
    BoundedCheckedCircuitRunCertificate
      sigma witness mode (.not circuit) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hmodeParts :
      tagAllowed mode .neg = true ∧
        modeCheck (childMode mode .neg) circuit = true := by
    have h := hmode
    rw [modeCheck_not] at h
    simpa using h
  have hAllowed : tagAllowed mode .neg = true := hmodeParts.1
  have hchildMode :
      modeCheck (childMode mode .neg) circuit = true := hmodeParts.2

  have hlenChild :
      CanonicalSATWitness.varBound circuit ≤ witness.length := by
    simpa [CanonicalSATWitness.varBound] using hlen
  have hreadChild :
      ∀ i, i < CanonicalSATWitness.varBound circuit →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by
      simpa [CanonicalSATWitness.varBound] using hi)

  have hLayoutTag :
      CheckedLayoutBound n consumed
        (false :: true :: true :: (encodeCircuit circuit ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  have hLayoutChildRaw :=
    P01CheckedVerifierInvariant.after_push_tag
      n consumed false true true
      (encodeCircuit circuit ++ tail)
      (encodeEvalFrames frames) .neg hLayoutTag
  have hLayoutChild :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit circuit ++ tail)
        (encodeEvalFrames (.neg :: frames)) := by
    simpa [encodeEvalFrames, List.append_assoc] using hLayoutChildRaw

  have hsource :
      (false :: true :: true :: (encodeCircuit circuit ++ tail)).length ≤ n :=
    hLayoutTag.source_le
  have hframes : (encodeEvalFrames frames).length ≤ n :=
    hLayoutTag.frames_le

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness (encodeCircuit circuit ++ tail)
      (encodeEvalFrames frames) consumed padding
      false true true .neg .neg
      (by rfl) hAllowed
      (by simp [P01CheckedEvalRunTagPrefix.postTagState])
      hsource hframes

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : CheckedConfig :=
    { state := .need (childMode mode .neg)
        needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit circuit ++ tail)
          (encodeEvalFrames (.neg :: frames))
          padChild }

  have h0' :
      cNeed ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not circuit) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild, encodeCircuit, encodeEvalFrames,
      List.append_assoc] using h0

  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild n
      hLayoutChild hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  have hchildInput : ∃ i, circuit = .input i := by
    have hm : modeCheck .mustInput circuit = true := by
      simpa [childMode] using hchildMode
    exact (modeCheck_mustInput_iff circuit).1 hm

  have houtHave :
      ∃ consumed1 padding1,
        cfg1 =
          { state := .have .mustInput
              (.start (evalCircuit sigma circuit)),
            tape :=
              evalCursorStackEndTape witness consumed1 tail
                (encodeEvalFrames (.neg :: frames)) padding1 } := by
    rcases hchildInput with ⟨i, rfl⟩
    simpa [CheckedLoopOutcome, exitMode, childMode, circuitTag] using hout1

  rcases houtHave with ⟨consumed1, padding1, hcfg1⟩
  subst cfg1

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_checked_reaches_have
      .mustInput witness tail (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma circuit)

  let cHave : CheckedConfig :=
    { state := .have .mustInput
        (.start (!(evalCircuit sigma circuit))),
      tape :=
        evalCursorStackEndTape witness consumed1 tail
          (encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have .mustInput
               (.start (evalCircuit sigma circuit)),
             tape :=
               evalCursorStackEndTape witness consumed1 tail
                 (encodeEvalFrames (.neg :: frames)) padding1 }] := by
    simpa [cHave, encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have .mustInput
           (.start (evalCircuit sigma circuit)),
         tape :=
           evalCursorStackEndTape witness consumed1 tail
             (encodeEvalFrames (.neg :: frames)) padding1 } : CheckedConfig)
      cHave h01 h2'

  obtain ⟨m3, hm3, cfgFinal, h3, hout3⟩ :=
    have_reaches_outcome_within_envelope
      n .mustInput witness (!(evalCircuit sigma circuit))
      tail frames consumed1 (padding1 + 3)

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h012 h3

  have hm2L : m2 ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans hm2 (nine_le_stepEnvelope n)
  have hside :
      m0 + m2 + m3 ≤ 3 * checkedLoopStepEnvelope n := by
    omega
  have hcoef :
      8 * (evalStepCount circuit + 1) + 3 ≤
        8 * (evalStepCount (.not circuit) + 1) := by
    simp [evalStepCount]
    omega
  have hbudget :
      checkedCircuitBudget circuit n +
          3 * checkedLoopStepEnvelope n ≤
        checkedCircuitBudget (.not circuit) n := by
    have hmul :=
      Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hcoef
    simpa [checkedCircuitBudget, Nat.add_mul] using hmul
  have htotal :
      m0 + m1 + m2 + m3 ≤
        checkedCircuitBudget (.not circuit) n := by
    calc
      m0 + m1 + m2 + m3
          = m1 + (m0 + m2 + m3) := by omega
      _ ≤ checkedCircuitBudget circuit n +
            3 * checkedLoopStepEnvelope n :=
        Nat.add_le_add hm1 hside
      _ ≤ checkedCircuitBudget (.not circuit) n := hbudget

  refine ⟨m0 + m1 + m2 + m3, htotal, cfgFinal, hAll, ?_⟩
  simpa [CheckedLoopOutcome, exitMode, childMode,
    circuitTag, evalCircuit] using hout3

#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.loopEnvelope_le_checkedCircuitBudget
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.input_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunBoundedCertificate.const_bounded_certificate

end P01CheckedEvalRunBoundedCertificate
end Real
end MCore
