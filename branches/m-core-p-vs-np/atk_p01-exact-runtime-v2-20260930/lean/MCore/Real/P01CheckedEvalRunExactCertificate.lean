import MCore.Real.P01CheckedEvalRunBoundedCertificate

namespace MCore
namespace Real
namespace P01CheckedEvalRunExactCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01InputNodeRoundTrip
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunInputTag
open P01CheckedEvalRunBoundedInput
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/--
Strengthened checked-loop outcome carrying the exact number of source cells
consumed by one canonical circuit prefix.

For a terminal root run with empty tail and frames the ordinary checked outcome
already records the final state, so no cursor is externally visible. In every
continuation case the cursor is required to be exactly the initial consumed
count plus the canonical encoded circuit length.
-/
def ExactCheckedLoopOutcome
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed : Nat)
    (phi : CircuitK1.Circuit)
    (cfg : CheckedConfig) : Prop :=
  CheckedLoopOutcome witness mode value tail frames cfg ∧
  match tail, frames with
  | [], [] => True
  | _, _ =>
      ∃ padding' : Nat,
        cfg =
          { state := .have mode (.start value),
            tape :=
              evalCursorStackEndTape witness
                (consumed + (encodeCircuit phi).length)
                tail (encodeEvalFrames frames) padding' }

/--
Bounded checked certificate with an exact physical consumption law.

This is the compositional form needed by binary constructors: after the left
child returns, the right child receives a proved CheckedLayoutBound at the
exact updated source cursor rather than an existentially hidden cursor.
-/
def ExactBoundedCheckedCircuitRunCertificate
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
      ExactCheckedLoopOutcome witness (exitMode mode phi)
        (evalCircuit sigma phi) tail frames consumed phi cfg

/--
When unread source remains, exact outcome exposes the unique expected consumed
counter directly.
-/
theorem exact_outcome_have_of_tail_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed : Nat)
    (phi : CircuitK1.Circuit)
    (cfg : CheckedConfig)
    (htail : tail ≠ [])
    (h :
      ExactCheckedLoopOutcome witness mode value tail frames
        consumed phi cfg) :
    ∃ padding' : Nat,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness
              (consumed + (encodeCircuit phi).length)
              tail (encodeEvalFrames frames) padding' } := by
  rcases h with ⟨hout, hexact⟩
  cases tail with
  | nil => exact False.elim (htail rfl)
  | cons b bs =>
      simpa [ExactCheckedLoopOutcome] using hexact

/--
When the source tail is empty but a continuation frame remains, exact outcome
still exposes the exact consumed counter.
-/
theorem exact_outcome_have_of_frames_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (frames : List EvalFrame)
    (consumed : Nat)
    (phi : CircuitK1.Circuit)
    (cfg : CheckedConfig)
    (hframes : frames ≠ [])
    (h :
      ExactCheckedLoopOutcome witness mode value [] frames
        consumed phi cfg) :
    ∃ padding' : Nat,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness
              (consumed + (encodeCircuit phi).length)
              [] (encodeEvalFrames frames) padding' } := by
  rcases h with ⟨hout, hexact⟩
  cases frames with
  | nil => exact False.elim (hframes rfl)
  | cons f fs =>
      simpa [ExactCheckedLoopOutcome] using hexact

/-- Exact consumption strictly strengthens the existing bounded certificate. -/
theorem exact_to_bounded
    {sigma : Assignment}
    {witness : BitString}
    {mode : SyntaxMode}
    {phi : CircuitK1.Circuit}
    (h : ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode phi) :
    BoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  obtain ⟨m, hm, cfg, hrun, hout⟩ :=
    h hmode tail frames consumed padding n hLayout hlen hread
  exact ⟨m, hm, cfg, hrun, hout.1⟩

/-- Canonical input-node consumption is exactly its encoded prefix length. -/
theorem input_consumed_exact
    (consumed i : Nat) :
    consumedAfterInputIndex (consumed + 3) i =
      consumed + (encodeCircuit (.input i)).length := by
  simp [consumedAfterInputIndex, encodeCircuit,
    CanonicalSATWitness.encodeNat_length]
  omega

/--
Input leaf inhabits the strengthened bounded certificate.

The physical indexed reader already exposes its final cursor, so no new
machine argument is introduced here: the theorem only retains the exact cursor
equation that the weaker bounded certificate erased.
-/
theorem input_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.input i) := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar
  have hmodeExit :
      mode = P01CheckedEvalRunBaseCases.exitMode mode (.input i) := by
    simp [P01CheckedEvalRunBaseCases.exitMode, circuitTag, childMode]
  have hvalueElem :
      witness[i]?.getD false = sigma i := by
    simpa [List.getD_eq_getElem?_getD] using hvalue

  have hLayoutInput :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_within_loopEnvelope
      n mode witness tail (encodeEvalFrames frames)
      consumed padding i hi hLayoutInput

  let consumed' := consumedAfterInputIndex (consumed + 3) i
  let cfg : CheckedConfig :=
    inputCheckedConfig mode
      ({ state :=
           .done (witness.getD i false)
             (inputNodeFinalMode tail (encodeEvalFrames frames)),
         tape :=
           (inputAfterReadTarget witness consumed'
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration InputNodeCompositeState (Option Bool))

  refine ⟨m,
    Nat.le_trans hm
      (loopEnvelope_le_checkedCircuitBudget (.input i) n),
    cfg, ?_, ?_⟩
  · simpa [cfg, consumed', encodeCircuit] using hrun
  · constructor
    · change CheckedLoopOutcome witness (exitMode mode (.input i))
        (sigma i) tail frames cfg
      rw [← hvalue]
      cases tail with
      | cons b bs =>
          refine ⟨consumed', padding, ?_⟩
          simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
            cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
            inputNodeFinalMode, inputAfterReadTarget]
      | nil =>
          cases frames with
          | nil =>
              refine ⟨(inputAfterReadTarget witness consumed'
                [] [] padding).tape, ?_⟩
              simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                inputNodeFinalMode, inputAfterReadTarget]
          | cons f fs =>
              refine ⟨consumed', padding, ?_⟩
              cases f with
              | neg =>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | andLeft =>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | andRight b =>
                  cases b <;>
                    simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                      cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                      inputNodeFinalMode, inputAfterReadTarget,
                      encodeEvalFrames, encodeEvalFrame]
              | orLeft =>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | orRight b =>
                  cases b <;>
                    simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                      cfg, consumed', inputCheckedConfig, inputCheckedEmbed,
                      inputNodeFinalMode, inputAfterReadTarget,
                      encodeEvalFrames, encodeEvalFrame]
    · cases tail with
      | nil =>
          cases frames with
          | nil =>
              trivial
          | cons f fs =>
              refine ⟨padding, ?_⟩
              cases f with
              | neg =>
                  simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
                    input_consumed_exact, cfg, consumed',
                    inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | andLeft =>
                  simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
                    input_consumed_exact, cfg, consumed',
                    inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | andRight b =>
                  cases b <;>
                    simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
                      input_consumed_exact, cfg, consumed',
                      inputCheckedConfig, inputCheckedEmbed,
                      inputNodeFinalMode, inputAfterReadTarget,
                      encodeEvalFrames, encodeEvalFrame]
              | orLeft =>
                  simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
                    input_consumed_exact, cfg, consumed',
                    inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
              | orRight b =>
                  cases b <;>
                    simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
                      input_consumed_exact, cfg, consumed',
                      inputCheckedConfig, inputCheckedEmbed,
                      inputNodeFinalMode, inputAfterReadTarget,
                      encodeEvalFrames, encodeEvalFrame]
      | cons b bs =>
          refine ⟨padding, ?_⟩
          simp [ExactCheckedLoopOutcome, evalCircuit, hvalue, hmodeExit, hvalueElem,
            input_consumed_exact, cfg, consumed',
            inputCheckedConfig, inputCheckedEmbed,
            inputNodeFinalMode, inputAfterReadTarget]

#print axioms MCore.Real.P01CheckedEvalRunExactCertificate.exact_outcome_have_of_tail_ne_nil
#print axioms MCore.Real.P01CheckedEvalRunExactCertificate.exact_outcome_have_of_frames_ne_nil
#print axioms MCore.Real.P01CheckedEvalRunExactCertificate.input_consumed_exact
#print axioms MCore.Real.P01CheckedEvalRunExactCertificate.input_exact_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunExactCertificate.exact_to_bounded

end P01CheckedEvalRunExactCertificate
end Real
end MCore
