import MCore.Real.P01DecodeFailureLaws
import MCore.Real.P01ExactBoundedAll
import MCore.Real.P01CheckedEvalRejectBounded
import MCore.Real.P01MalformedRawBoundedReject

namespace MCore
namespace Real
namespace P01CoreDecodeFailurePhysical

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalRejectBounded
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01ExactBoundedAll
open P01MaterialGlobalBudget
open P01CoreDecodeFailureAtoms
open P01DecodeFailureLaws
open P01DecodeCoreLaws
open P01MalformedRawBoundedReject
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/--
Source-length potential for malformed recursive decoding.

One source cell owns 32 checked-loop envelopes.  This is deliberately chosen
so that:
* a three-bit constructor pays for its physical dispatch;
* a successfully decoded left child can be physically evaluated;
* the continuation handoff can be paid;
* the remaining source still owns enough potential for recursive failure.

At the top level this potential is bounded by the existing 8192-cubic material
verifier budget.
-/
def coreRejectBudget (sourceLen n : Nat) : Nat :=
  32 * (sourceLen + 1) * checkedLoopStepEnvelope n

theorem coreRejectBudget_le_material
    (sourceLen n : Nat)
    (hsource : sourceLen ≤ n) :
    coreRejectBudget sourceLen n ≤ materialVerifierGlobalTimeBound n := by
  have hcoef :
      32 * (sourceLen + 1) ≤ 32 * (n + 1) :=
    Nat.mul_le_mul_left 32 (Nat.add_le_add_right hsource 1)
  have hmul :=
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hcoef
  calc
    coreRejectBudget sourceLen n
        ≤ 32 * (n + 1) * checkedLoopStepEnvelope n := by
          simpa [coreRejectBudget] using hmul
    _ = materialVerifierGlobalTimeBound n := by
          simp [checkedLoopStepEnvelope, materialVerifierGlobalTimeBound,
            Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem loopEnvelope_le_coreRejectBudget
    (sourceLen n : Nat) :
    checkedLoopStepEnvelope n ≤ coreRejectBudget sourceLen n := by
  let E := checkedLoopStepEnvelope n
  have hcoef : 1 ≤ 32 * (sourceLen + 1) := by omega
  have hmul := Nat.mul_le_mul_right E hcoef
  simpa [coreRejectBudget, E] using hmul

private theorem root_plus_recursive_budget
    (restLen n : Nat) :
    checkedLoopStepEnvelope n + coreRejectBudget restLen n ≤
      coreRejectBudget (restLen + 3) n := by
  let E := checkedLoopStepEnvelope n
  have hcoef :
      1 + 32 * (restLen + 1) ≤
        32 * ((restLen + 3) + 1) := by omega
  have hmul := Nat.mul_le_mul_right E hcoef
  calc
    checkedLoopStepEnvelope n + coreRejectBudget restLen n
        = (1 + 32 * (restLen + 1)) * E := by
            unfold coreRejectBudget
            dsimp [E]
            rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 32 * ((restLen + 3) + 1) * E := hmul
    _ = coreRejectBudget (restLen + 3) n := by
          rfl

private theorem root_plus_circuit_budget
    (phi : Circuit) (tailLen n : Nat) :
    checkedLoopStepEnvelope n + checkedCircuitBudget phi n ≤
      coreRejectBudget (3 + (encodeCircuit phi).length + tailLen) n := by
  let E := checkedLoopStepEnvelope n
  have hs := evalStepCount_le_three_mul_encoding phi
  have hcoef :
      1 + 8 * (evalStepCount phi + 1) ≤
        32 * ((3 + (encodeCircuit phi).length + tailLen) + 1) := by
    omega
  have hmul := Nat.mul_le_mul_right E hcoef
  calc
    checkedLoopStepEnvelope n + checkedCircuitBudget phi n
        = (1 + 8 * (evalStepCount phi + 1)) * E := by
            unfold checkedCircuitBudget
            dsimp [E]
            rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 32 * ((3 + (encodeCircuit phi).length + tailLen) + 1) * E := hmul
    _ = coreRejectBudget (3 + (encodeCircuit phi).length + tailLen) n := by
          rfl

private theorem root_eval_handoff_recursive_budget
    (phi : Circuit) (tailLen n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n +
        coreRejectBudget tailLen n ≤
      coreRejectBudget (3 + (encodeCircuit phi).length + tailLen) n := by
  let E := checkedLoopStepEnvelope n
  have hs := evalStepCount_le_three_mul_encoding phi
  have hcoef :
      1 + 8 * (evalStepCount phi + 1) + 1 +
          32 * (tailLen + 1) ≤
        32 * ((3 + (encodeCircuit phi).length + tailLen) + 1) := by
    omega
  have hmul := Nat.mul_le_mul_right E hcoef
  calc
    checkedLoopStepEnvelope n +
          checkedCircuitBudget phi n +
          checkedLoopStepEnvelope n +
          coreRejectBudget tailLen n
        =
      (1 + 8 * (evalStepCount phi + 1) + 1 +
          32 * (tailLen + 1)) * E := by
            unfold checkedCircuitBudget coreRejectBudget
            dsimp [E]
            simp only [Nat.add_mul, Nat.one_mul]
            ac_rfl
    _ ≤ 32 * ((3 + (encodeCircuit phi).length + tailLen) + 1) * E := hmul
    _ = coreRejectBudget (3 + (encodeCircuit phi).length + tailLen) n := by
          rfl

theorem encodeCircuit_three_le
    (phi : Circuit) :
    3 ≤ (encodeCircuit phi).length := by
  cases phi <;> simp [encodeCircuit] <;> omega

/-- Unary payload decoder failure rejects inside a single loop envelope. -/
theorem input_decode_failure_rejects_loopEnvelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hdecode : decodeNat rest = none)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (false :: false :: false :: rest)
                   (encodeEvalFrames frames) padding }] := by
  have hrep := P01DecodeCoreLaws.decodeNat_none_eq_replicate_true rest hdecode
  obtain ⟨m, hm, tape, hrun⟩ :=
    P01CheckedEvalRunInputTag.inputTag_unterminated_reaches_reject
      mode witness (encodeEvalFrames frames) consumed padding rest.length
  have hfuel :
      P01CheckedEvalRunInputTag.checkedUnterminatedInputFuel
          rest.length (encodeEvalFrames frames) ≤
        3 * n + 13 := by
    unfold P01CheckedEvalRunInputTag.checkedUnterminatedInputFuel
      P01CheckedEvalRunTagPrefix.checkedTagPrefixFuel
    simp
    omega
  have hbase : n + 1 ≤ (n + 1)^2 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hp
      _ = (n + 1)^2 := by simp [Nat.pow_two]
  have hlinear : 3 * n + 13 ≤ 16 * (n + 1) := by omega
  have hscale :
      16 * (n + 1) ≤ 16 * (n + 1)^2 :=
    Nat.mul_le_mul_left 16 hbase
  have htoLoop :
      16 * (n + 1)^2 ≤ checkedLoopStepEnvelope n := by
    unfold checkedLoopStepEnvelope
    exact Nat.mul_le_mul_right ((n + 1)^2) (by omega)
  refine ⟨m,
    Nat.le_trans hm
      (Nat.le_trans hfuel
        (Nat.le_trans hlinear
          (Nat.le_trans hscale htoLoop))),
    tape, ?_⟩
  simpa [hrep] using hrun

/--
General recursive physical rejection theorem.

The critical precondition is `source.length < fuel`: the functional decoder
has enough recursion fuel to inspect every possible constructor represented by
the source.  Therefore `decodeCircuitCore fuel source = none` denotes a real
malformed source rather than artificial fuel exhaustion.
-/
theorem decodeCore_none_reaches_reject :
    ∀ fuel : Nat,
      ∀ (mode : SyntaxMode)
        (witness source : BitString)
        (frames : List EvalFrame)
        (consumed padding n : Nat),
      source.length < fuel →
      n ≤ witness.length →
      CheckedLayoutBound n consumed source (encodeEvalFrames frames) →
      decodeCircuitCore fuel source = none →
      ∃ m ≤ coreRejectBudget source.length n, ∃ cfg : CheckedConfig,
        cfg ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed source
                   (encodeEvalFrames frames) padding }] ∧
        cfg.state = .reject := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode witness source frames consumed padding n hlt hnw hLayout hdec
      omega
  | succ fuel ih =>
      intro mode witness source frames consumed padding n hlt hnw hLayout hdec
      have hcases :=
        decodeCore_none_cases fuel source (by
          simpa [Nat.succ_eq_add_one] using hdec)
      rcases hcases with hshort | hinput | hnot | hand | hor | hinvalid
      · obtain ⟨m, hm, tape, hrun⟩ :=
          short_tag_reaches_reject_within_envelope
            n mode witness source (encodeEvalFrames frames)
            consumed padding hshort hLayout.source_le hLayout.frames_le
        let cfg : CheckedConfig := { state := .reject, tape := tape }
        refine ⟨m,
          Nat.le_trans hm (loopEnvelope_le_coreRejectBudget source.length n),
          cfg, ?_, rfl⟩
        simpa [cfg] using hrun
      · rcases hinput with ⟨rest, rfl, hnat⟩
        have hrest : rest.length ≤ n := by
          have hs := hLayout.source_le
          simp at hs
          omega
        obtain ⟨m, hm, tape, hrun⟩ :=
          input_decode_failure_rejects_loopEnvelope
            n mode witness rest frames consumed padding
            hnat hrest hLayout.frames_le
        let cfg : CheckedConfig := { state := .reject, tape := tape }
        refine ⟨m,
          Nat.le_trans hm
            (loopEnvelope_le_coreRejectBudget
              (false :: false :: false :: rest).length n),
          cfg, ?_, rfl⟩
        simpa [cfg] using hrun
      · rcases hnot with ⟨rest, rfl, hchildNone⟩
        cases hallowed : tagAllowed mode .neg with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding false true true
                (by simpa using hallowed)
                hLayout.source_le hLayout.frames_le
            let cfg : CheckedConfig :=
              { state := .reject,
                tape :=
                  evalCursorReadTape witness (consumed + 3)
                    rest (encodeEvalFrames frames) padding }
            refine ⟨m,
              Nat.le_trans hm
                (loopEnvelope_le_coreRejectBudget
                  (false :: true :: true :: rest).length n),
              cfg, ?_, rfl⟩
            simpa [cfg] using hrun
        | true =>
            have hLayoutChildRaw :=
              after_push_tag n consumed false true true rest
                (encodeEvalFrames frames) .neg hLayout
            have hLayoutChild :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.neg :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using hLayoutChildRaw
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding false true true .neg .neg
                rfl hallowed rfl hLayout.source_le hLayout.frames_le
            let padChild := ((padding - 1) - 1) - 1
            let cChild : CheckedConfig :=
              { state := .need (childMode mode .neg)
                  needExprCompositeMachine.initial,
                tape :=
                  evalCursorStackEndTape witness (consumed + 3)
                    rest (encodeEvalFrames (.neg :: frames)) padChild }
            have h0' :
                cChild ∈
                  checkedEvalRunLoopMachine.runBranches m0
                    [{ state := .need mode needExprCompositeMachine.initial,
                       tape :=
                         evalCursorStackEndTape witness consumed
                           (false :: true :: true :: rest)
                           (encodeEvalFrames frames) padding }] := by
              simpa [cChild, padChild, encodeEvalFrames,
                List.append_assoc] using h0
            have hltChild : rest.length < fuel := by
              simp at hlt
              omega
            obtain ⟨m1, hm1, cfg, h1, hrej⟩ :=
              ih (childMode mode .neg) witness rest (.neg :: frames)
                (consumed + 3) padChild n
                hltChild hnw hLayoutChild hchildNone
            have h1' :
                cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cChild] := by
              simpa [cChild, padChild, encodeEvalFrames,
                List.append_assoc] using h1
            have hall :=
              mem_runBranches_trans checkedEvalRunLoopMachine
                m0 m1
                [{ state := .need mode needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness consumed
                       (false :: true :: true :: rest)
                       (encodeEvalFrames frames) padding }]
                cChild cfg h0' h1'
            have hbudget :
                m0 + m1 ≤
                  coreRejectBudget
                    (false :: true :: true :: rest).length n := by
              calc
                m0 + m1
                    ≤ checkedLoopStepEnvelope n +
                        coreRejectBudget rest.length n :=
                  Nat.add_le_add hm0 hm1
                _ ≤ coreRejectBudget (rest.length + 3) n :=
                  root_plus_recursive_budget rest.length n
                _ = coreRejectBudget
                    (false :: true :: true :: rest).length n := by simp
            exact ⟨m0 + m1, hbudget, cfg, hall, hrej⟩
      · rcases hand with ⟨rest, rfl, hfail⟩
        cases hallowed : tagAllowed mode .and with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false false
                (by simpa using hallowed)
                hLayout.source_le hLayout.frames_le
            let cfg : CheckedConfig :=
              { state := .reject,
                tape :=
                  evalCursorReadTape witness (consumed + 3)
                    rest (encodeEvalFrames frames) padding }
            refine ⟨m,
              Nat.le_trans hm
                (loopEnvelope_le_coreRejectBudget
                  (true :: false :: false :: rest).length n),
              cfg, ?_, rfl⟩
            simpa [cfg] using hrun
        | true =>
            have hmodeChild : childMode mode .and = .cnf := by
              cases mode <;> simp [tagAllowed, childMode] at hallowed ⊢
            have hLayoutLeftRaw :=
              after_push_tag n consumed true false false rest
                (encodeEvalFrames frames) .andLeft hLayout
            have hLayoutLeft :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.andLeft :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeftRaw
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false false .and .andLeft
                rfl hallowed
                (by simp [P01CheckedEvalRunTagPrefix.postTagState, hmodeChild])
                hLayout.source_le hLayout.frames_le
            let padLeft := ((padding - 1) - 1) - 1
            let cLeft : CheckedConfig :=
              { state := .need .cnf needExprCompositeMachine.initial,
                tape :=
                  evalCursorStackEndTape witness (consumed + 3)
                    rest (encodeEvalFrames (.andLeft :: frames)) padLeft }
            have h0' :
                cLeft ∈
                  checkedEvalRunLoopMachine.runBranches m0
                    [{ state := .need mode needExprCompositeMachine.initial,
                       tape :=
                         evalCursorStackEndTape witness consumed
                           (true :: false :: false :: rest)
                           (encodeEvalFrames frames) padding }] := by
              simpa [cLeft, padLeft, hmodeChild,
                encodeEvalFrames, List.append_assoc] using h0
            rcases hfail with hleftNone | hrightNone
            · have hltLeft : rest.length < fuel := by
                simp at hlt
                omega
              obtain ⟨m1, hm1, cfg, h1, hrej⟩ :=
                ih .cnf witness rest (.andLeft :: frames)
                  (consumed + 3) padLeft n
                  hltLeft hnw hLayoutLeft hleftNone
              have h1' :
                  cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cLeft] := by
                simpa [cLeft, padLeft, encodeEvalFrames,
                  List.append_assoc] using h1
              have hall :=
                mem_runBranches_trans checkedEvalRunLoopMachine
                  m0 m1
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: false :: rest)
                         (encodeEvalFrames frames) padding }]
                  cLeft cfg h0' h1'
              have hbudget :
                  m0 + m1 ≤
                    coreRejectBudget
                      (true :: false :: false :: rest).length n := by
                calc
                  m0 + m1
                      ≤ checkedLoopStepEnvelope n +
                          coreRejectBudget rest.length n :=
                    Nat.add_le_add hm0 hm1
                  _ ≤ coreRejectBudget (rest.length + 3) n :=
                    root_plus_recursive_budget rest.length n
                  _ = coreRejectBudget
                      (true :: false :: false :: rest).length n := by simp
              exact ⟨m0 + m1, hbudget, cfg, hall, hrej⟩
            · rcases hrightNone with ⟨a, rest', ha, hrightNone⟩
              have hshape : rest = encodeCircuit a ++ rest' :=
                decodeCircuitCore_sound fuel rest a rest' ha
              have hLayoutLeft' :
                  CheckedLayoutBound n (consumed + 3)
                    (encodeCircuit a ++ rest')
                    (encodeEvalFrames (.andLeft :: frames)) := by
                simpa [hshape] using hLayoutLeft
              let sigma : Assignment := fun i => witness.getD i false
              have hencN : (encodeCircuit a).length ≤ n := by
                exact Nat.le_trans
                  (by simp : (encodeCircuit a).length ≤
                    (encodeCircuit a ++ rest').length)
                  hLayoutLeft'.source_le
              have hlenA : varBound a ≤ witness.length :=
                Nat.le_trans varBound_le_encoded_length
                  (Nat.le_trans hencN hnw)
              have hreadA :
                  ∀ i, i < varBound a →
                    witness.getD i false = sigma i := by
                intro i hi
                rfl
              cases hmodeA : modeCheck .cnf a with
              | false =>
                  obtain ⟨ma, hma, cfg, hA, hrej⟩ :=
                    bounded_circuit_reject_certificate sigma witness a .cnf
                      hmodeA rest' (.andLeft :: frames)
                      (consumed + 3) padLeft n
                      hLayoutLeft' hlenA hreadA
                  have hA' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches ma [cLeft] := by
                    simpa [cLeft, padLeft, hshape, encodeEvalFrames,
                      List.append_assoc] using hA
                  have hall :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 ma
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      cLeft cfg h0' hA'
                  have hbudget :
                      m0 + ma ≤
                        coreRejectBudget
                          (true :: false :: false :: rest).length n := by
                    calc
                      m0 + ma
                          ≤ checkedLoopStepEnvelope n +
                              checkedCircuitBudget a n :=
                        Nat.add_le_add hm0 hma
                      _ ≤ coreRejectBudget
                          (3 + (encodeCircuit a).length + rest'.length) n :=
                        root_plus_circuit_budget a rest'.length n
                      _ = coreRejectBudget
                          (true :: false :: false :: rest).length n := by
                        simp [hshape, List.length_append]
                        omega
                  exact ⟨m0 + ma, hbudget, cfg, hall, hrej⟩
              | true =>
                  obtain ⟨ma, hma, cfgA, hA, houtA⟩ :=
                    exact_bounded_all sigma witness a .cnf
                      hmodeA rest' (.andLeft :: frames)
                      (consumed + 3) padLeft n
                      hLayoutLeft' hlenA hreadA
                  let leftConsumed :=
                    (consumed + 3) + (encodeCircuit a).length
                  have houtA' :
                      ∃ paddingA,
                        cfgA =
                          { state := .have (exitMode .cnf a)
                              (.start (evalCircuit sigma a)),
                            tape :=
                              evalCursorStackEndTape witness leftConsumed
                                rest' (encodeEvalFrames (.andLeft :: frames))
                                paddingA } := by
                    simpa [ExactCheckedLoopOutcome, leftConsumed] using houtA
                  rcases houtA' with ⟨paddingA, hcfgA⟩
                  subst cfgA
                  have hA' :
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.andLeft :: frames))
                             paddingA } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches ma [cLeft] := by
                    simpa [cLeft, padLeft, hshape, leftConsumed,
                      encodeEvalFrames, List.append_assoc] using hA
                  have h01 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 ma
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      cLeft
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.andLeft :: frames))
                             paddingA } : CheckedConfig)
                      h0' hA'
                  obtain ⟨m2, hm2, h2⟩ :=
                    andLeftReturn_checked_reaches_need_within_envelope
                      n (exitMode .cnf a) witness rest'
                      (encodeEvalFrames frames) leftConsumed paddingA
                      (evalCircuit sigma a)
                  let padRight := (((paddingA + 3) - 1) - 1) - 1
                  let cRight : CheckedConfig :=
                    { state := .need .cnf needExprCompositeMachine.initial,
                      tape :=
                        evalCursorStackEndTape witness leftConsumed rest'
                          (encodeEvalFrames
                            (.andRight (evalCircuit sigma a) :: frames))
                          padRight }
                  have h2' :
                      cRight ∈
                        checkedEvalRunLoopMachine.runBranches m2
                          [({ state := .have (exitMode .cnf a)
                               (.start (evalCircuit sigma a)),
                             tape :=
                               evalCursorStackEndTape witness leftConsumed
                                 rest' (encodeEvalFrames (.andLeft :: frames))
                                 paddingA } : CheckedConfig)] := by
                    simpa [cRight, padRight, encodeEvalFrames,
                      List.append_assoc] using h2
                  have h012 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + ma) m2
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.andLeft :: frames))
                             paddingA } : CheckedConfig)
                      cRight h01 h2'
                  have hLayoutAfterLeft :
                      CheckedLayoutBound n leftConsumed rest'
                        (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
                    simpa [leftConsumed, encodeEvalFrames, List.append_assoc] using
                      layout_consume_prefix n (consumed + 3)
                        (encodeCircuit a) rest'
                        (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
                        (by simpa [encodeEvalFrames, List.append_assoc] using
                          hLayoutLeft')
                  have hLayoutRightRaw :=
                    replace_top_frame n leftConsumed rest'
                      (encodeEvalFrames frames)
                      .andLeft (.andRight (evalCircuit sigma a))
                      hLayoutAfterLeft
                  have hLayoutRight :
                      CheckedLayoutBound n leftConsumed rest'
                        (encodeEvalFrames
                          (.andRight (evalCircuit sigma a) :: frames)) := by
                    simpa [encodeEvalFrames, List.append_assoc] using hLayoutRightRaw
                  have hltRight : rest'.length < fuel := by
                    have henc3 := encodeCircuit_three_le a
                    simp [hshape, List.length_append] at hlt
                    omega
                  obtain ⟨mr, hmr, cfg, hr, hrej⟩ :=
                    ih .cnf witness rest'
                      (.andRight (evalCircuit sigma a) :: frames)
                      leftConsumed padRight n
                      hltRight hnw hLayoutRight hrightNone
                  have hr' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches mr [cRight] := by
                    simpa [cRight, padRight, encodeEvalFrames,
                      List.append_assoc] using hr
                  have hall :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + ma + m2) mr
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      cRight cfg h012 hr'
                  have hbudget :
                      m0 + ma + m2 + mr ≤
                        coreRejectBudget
                          (true :: false :: false :: rest).length n := by
                    calc
                      m0 + ma + m2 + mr
                          ≤ checkedLoopStepEnvelope n +
                              checkedCircuitBudget a n +
                              checkedLoopStepEnvelope n +
                              coreRejectBudget rest'.length n := by
                        omega
                      _ ≤ coreRejectBudget
                          (3 + (encodeCircuit a).length + rest'.length) n :=
                        root_eval_handoff_recursive_budget
                          a rest'.length n
                      _ = coreRejectBudget
                          (true :: false :: false :: rest).length n := by
                        simp [hshape, List.length_append]
                        omega
                  exact ⟨m0 + ma + m2 + mr, hbudget, cfg, hall, hrej⟩
      · rcases hor with ⟨rest, rfl, hfail⟩
        cases hallowed : tagAllowed mode .or with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false true
                (by simpa using hallowed)
                hLayout.source_le hLayout.frames_le
            let cfg : CheckedConfig :=
              { state := .reject,
                tape :=
                  evalCursorReadTape witness (consumed + 3)
                    rest (encodeEvalFrames frames) padding }
            refine ⟨m,
              Nat.le_trans hm
                (loopEnvelope_le_coreRejectBudget
                  (true :: false :: true :: rest).length n),
              cfg, ?_, rfl⟩
            simpa [cfg] using hrun
        | true =>
            have hmodeChild : childMode mode .or = .clause := by
              cases mode <;> simp [tagAllowed, childMode] at hallowed ⊢
            have hLayoutLeftRaw :=
              after_push_tag n consumed true false true rest
                (encodeEvalFrames frames) .orLeft hLayout
            have hLayoutLeft :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.orLeft :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeftRaw
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false true .or .orLeft
                rfl hallowed
                (by simp [P01CheckedEvalRunTagPrefix.postTagState, hmodeChild])
                hLayout.source_le hLayout.frames_le
            let padLeft := ((padding - 1) - 1) - 1
            let cLeft : CheckedConfig :=
              { state := .need .clause needExprCompositeMachine.initial,
                tape :=
                  evalCursorStackEndTape witness (consumed + 3)
                    rest (encodeEvalFrames (.orLeft :: frames)) padLeft }
            have h0' :
                cLeft ∈
                  checkedEvalRunLoopMachine.runBranches m0
                    [{ state := .need mode needExprCompositeMachine.initial,
                       tape :=
                         evalCursorStackEndTape witness consumed
                           (true :: false :: true :: rest)
                           (encodeEvalFrames frames) padding }] := by
              simpa [cLeft, padLeft, hmodeChild,
                encodeEvalFrames, List.append_assoc] using h0
            rcases hfail with hleftNone | hrightNone
            · have hltLeft : rest.length < fuel := by
                simp at hlt
                omega
              obtain ⟨m1, hm1, cfg, h1, hrej⟩ :=
                ih .clause witness rest (.orLeft :: frames)
                  (consumed + 3) padLeft n
                  hltLeft hnw hLayoutLeft hleftNone
              have h1' :
                  cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cLeft] := by
                simpa [cLeft, padLeft, encodeEvalFrames,
                  List.append_assoc] using h1
              have hall :=
                mem_runBranches_trans checkedEvalRunLoopMachine
                  m0 m1
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: true :: rest)
                         (encodeEvalFrames frames) padding }]
                  cLeft cfg h0' h1'
              have hbudget :
                  m0 + m1 ≤
                    coreRejectBudget
                      (true :: false :: true :: rest).length n := by
                calc
                  m0 + m1
                      ≤ checkedLoopStepEnvelope n +
                          coreRejectBudget rest.length n :=
                    Nat.add_le_add hm0 hm1
                  _ ≤ coreRejectBudget (rest.length + 3) n :=
                    root_plus_recursive_budget rest.length n
                  _ = coreRejectBudget
                      (true :: false :: true :: rest).length n := by simp
              exact ⟨m0 + m1, hbudget, cfg, hall, hrej⟩
            · rcases hrightNone with ⟨a, rest', ha, hrightNone⟩
              have hshape : rest = encodeCircuit a ++ rest' :=
                decodeCircuitCore_sound fuel rest a rest' ha
              have hLayoutLeft' :
                  CheckedLayoutBound n (consumed + 3)
                    (encodeCircuit a ++ rest')
                    (encodeEvalFrames (.orLeft :: frames)) := by
                simpa [hshape] using hLayoutLeft
              let sigma : Assignment := fun i => witness.getD i false
              have hencN : (encodeCircuit a).length ≤ n := by
                exact Nat.le_trans
                  (by simp : (encodeCircuit a).length ≤
                    (encodeCircuit a ++ rest').length)
                  hLayoutLeft'.source_le
              have hlenA : varBound a ≤ witness.length :=
                Nat.le_trans varBound_le_encoded_length
                  (Nat.le_trans hencN hnw)
              have hreadA :
                  ∀ i, i < varBound a →
                    witness.getD i false = sigma i := by
                intro i hi
                rfl
              cases hmodeA : modeCheck .clause a with
              | false =>
                  obtain ⟨ma, hma, cfg, hA, hrej⟩ :=
                    bounded_circuit_reject_certificate sigma witness a .clause
                      hmodeA rest' (.orLeft :: frames)
                      (consumed + 3) padLeft n
                      hLayoutLeft' hlenA hreadA
                  have hA' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches ma [cLeft] := by
                    simpa [cLeft, padLeft, hshape, encodeEvalFrames,
                      List.append_assoc] using hA
                  have hall :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 ma
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      cLeft cfg h0' hA'
                  have hbudget :
                      m0 + ma ≤
                        coreRejectBudget
                          (true :: false :: true :: rest).length n := by
                    calc
                      m0 + ma
                          ≤ checkedLoopStepEnvelope n +
                              checkedCircuitBudget a n :=
                        Nat.add_le_add hm0 hma
                      _ ≤ coreRejectBudget
                          (3 + (encodeCircuit a).length + rest'.length) n :=
                        root_plus_circuit_budget a rest'.length n
                      _ = coreRejectBudget
                          (true :: false :: true :: rest).length n := by
                        simp [hshape, List.length_append]
                        omega
                  exact ⟨m0 + ma, hbudget, cfg, hall, hrej⟩
              | true =>
                  obtain ⟨ma, hma, cfgA, hA, houtA⟩ :=
                    exact_bounded_all sigma witness a .clause
                      hmodeA rest' (.orLeft :: frames)
                      (consumed + 3) padLeft n
                      hLayoutLeft' hlenA hreadA
                  let leftConsumed :=
                    (consumed + 3) + (encodeCircuit a).length
                  have houtA' :
                      ∃ paddingA,
                        cfgA =
                          { state := .have (exitMode .clause a)
                              (.start (evalCircuit sigma a)),
                            tape :=
                              evalCursorStackEndTape witness leftConsumed
                                rest' (encodeEvalFrames (.orLeft :: frames))
                                paddingA } := by
                    simpa [ExactCheckedLoopOutcome, leftConsumed] using houtA
                  rcases houtA' with ⟨paddingA, hcfgA⟩
                  subst cfgA
                  have hA' :
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.orLeft :: frames))
                             paddingA } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches ma [cLeft] := by
                    simpa [cLeft, padLeft, hshape, leftConsumed,
                      encodeEvalFrames, List.append_assoc] using hA
                  have h01 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 ma
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      cLeft
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.orLeft :: frames))
                             paddingA } : CheckedConfig)
                      h0' hA'
                  obtain ⟨m2, hm2, h2⟩ :=
                    orLeftReturn_checked_reaches_need_within_envelope
                      n (exitMode .clause a) witness rest'
                      (encodeEvalFrames frames) leftConsumed paddingA
                      (evalCircuit sigma a)
                  let padRight := (((paddingA + 3) - 1) - 1) - 1
                  let cRight : CheckedConfig :=
                    { state := .need .clause needExprCompositeMachine.initial,
                      tape :=
                        evalCursorStackEndTape witness leftConsumed rest'
                          (encodeEvalFrames
                            (.orRight (evalCircuit sigma a) :: frames))
                          padRight }
                  have h2' :
                      cRight ∈
                        checkedEvalRunLoopMachine.runBranches m2
                          [({ state := .have (exitMode .clause a)
                               (.start (evalCircuit sigma a)),
                             tape :=
                               evalCursorStackEndTape witness leftConsumed
                                 rest' (encodeEvalFrames (.orLeft :: frames))
                                 paddingA } : CheckedConfig)] := by
                    simpa [cRight, padRight, encodeEvalFrames,
                      List.append_assoc] using h2
                  have h012 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + ma) m2
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness leftConsumed
                             rest' (encodeEvalFrames (.orLeft :: frames))
                             paddingA } : CheckedConfig)
                      cRight h01 h2'
                  have hLayoutAfterLeft :
                      CheckedLayoutBound n leftConsumed rest'
                        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
                    simpa [leftConsumed, encodeEvalFrames, List.append_assoc] using
                      layout_consume_prefix n (consumed + 3)
                        (encodeCircuit a) rest'
                        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
                        (by simpa [encodeEvalFrames, List.append_assoc] using
                          hLayoutLeft')
                  have hLayoutRightRaw :=
                    replace_top_frame n leftConsumed rest'
                      (encodeEvalFrames frames)
                      .orLeft (.orRight (evalCircuit sigma a))
                      hLayoutAfterLeft
                  have hLayoutRight :
                      CheckedLayoutBound n leftConsumed rest'
                        (encodeEvalFrames
                          (.orRight (evalCircuit sigma a) :: frames)) := by
                    simpa [encodeEvalFrames, List.append_assoc] using hLayoutRightRaw
                  have hltRight : rest'.length < fuel := by
                    have henc3 := encodeCircuit_three_le a
                    simp [hshape, List.length_append] at hlt
                    omega
                  obtain ⟨mr, hmr, cfg, hr, hrej⟩ :=
                    ih .clause witness rest'
                      (.orRight (evalCircuit sigma a) :: frames)
                      leftConsumed padRight n
                      hltRight hnw hLayoutRight hrightNone
                  have hr' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches mr [cRight] := by
                    simpa [cRight, padRight, encodeEvalFrames,
                      List.append_assoc] using hr
                  have hall :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + ma + m2) mr
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      cRight cfg h012 hr'
                  have hbudget :
                      m0 + ma + m2 + mr ≤
                        coreRejectBudget
                          (true :: false :: true :: rest).length n := by
                    calc
                      m0 + ma + m2 + mr
                          ≤ checkedLoopStepEnvelope n +
                              checkedCircuitBudget a n +
                              checkedLoopStepEnvelope n +
                              coreRejectBudget rest'.length n := by
                        omega
                      _ ≤ coreRejectBudget
                          (3 + (encodeCircuit a).length + rest'.length) n :=
                        root_eval_handoff_recursive_budget
                          a rest'.length n
                      _ = coreRejectBudget
                          (true :: false :: true :: rest).length n := by
                        simp [hshape, List.length_append]
                        omega
                  exact ⟨m0 + ma + m2 + mr, hbudget, cfg, hall, hrej⟩
      · rcases hinvalid with ⟨third, rest, rfl⟩
        have hdis :
            tagAllowed mode
              (P01NeedExprTagDecode.decodeTagBits true true third) = false := by
          cases mode <;> cases third <;> rfl
        obtain ⟨m, hm, hrun⟩ :=
          disallowed_tag_prefix_reaches_reject_within_envelope
            n mode witness rest (encodeEvalFrames frames)
            consumed padding true true third hdis
            hLayout.source_le hLayout.frames_le
        let cfg : CheckedConfig :=
          { state := .reject,
            tape :=
              evalCursorReadTape witness (consumed + 3)
                rest (encodeEvalFrames frames) padding }
        refine ⟨m,
          Nat.le_trans hm
            (loopEnvelope_le_coreRejectBudget
              (true :: true :: third :: rest).length n),
          cfg, ?_, rfl⟩
        simpa [cfg] using hrun

/-- The remaining raw decoder gap is inhabited without endpoint assumptions. -/
theorem core_decode_failure_physical_reject :
    CoreDecodeFailurePhysicalReject := by
  intro witness bs hw hdecode
  have hlt : bs.length < bs.length + 1 := by omega
  have hnw : bs.length ≤ witness.length := by omega
  have hLayout :
      CheckedLayoutBound bs.length 0 bs (encodeEvalFrames []) := by
    simpa using CheckedLayoutBound.root bs
  obtain ⟨m, hm, cfg, hrun, hrej⟩ :=
    decodeCore_none_reaches_reject
      (bs.length + 1) .cnf witness bs [] 0 0 bs.length
      hlt hnw hLayout hdecode
  exact ⟨m,
    Nat.le_trans hm
      (coreRejectBudget_le_material bs.length bs.length (Nat.le_refl _)),
    cfg, by simpa using hrun, hrej⟩

#print axioms MCore.Real.P01CoreDecodeFailurePhysical.coreRejectBudget_le_material
#print axioms MCore.Real.P01CoreDecodeFailurePhysical.decodeCore_none_reaches_reject
#print axioms MCore.Real.P01CoreDecodeFailurePhysical.core_decode_failure_physical_reject

end P01CoreDecodeFailurePhysical
end Real
end MCore
