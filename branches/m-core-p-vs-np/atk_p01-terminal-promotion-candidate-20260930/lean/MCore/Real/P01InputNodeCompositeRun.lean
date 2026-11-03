import MCore.Real.P01InputNodeCompositeNTM
import MCore.Real.P01InputNodeRoundTrip
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01InputNodeCompositeRun

open CanonicalFinalProof
open P01NTMRunLaws
open P01InputReturnMode
open P01InputIndexLookahead
open P01WitnessIndexedReadPreserving
open P01InputAfterReadReturn
open P01InputNodeCompositeNTM
open P01InputNodeRoundTrip
open P01EvalCursorMachine
open P01WitnessIndexedReadGap
open CanonicalCircuitBits

abbrev CompositeConfig :=
  Configuration InputNodeCompositeState (Option Bool)

def lookConfig
    (c : Configuration InputIndexLookaheadState (Option Bool)) :
    CompositeConfig :=
  { state := .look c.state, tape := c.tape }

def readConfig
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool)) :
    CompositeConfig :=
  { state := .read mode c.state, tape := c.tape }

def returnConfig
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool)) :
    CompositeConfig :=
  { state := .ret mode selected c.state, tape := c.tape }

@[simp] theorem lookConfig_not_halted
    (c : Configuration InputIndexLookaheadState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (lookConfig c) := by
  simp [Halted, lookConfig, inputNodeCompositeMachine]

@[simp] theorem readConfig_not_halted
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (readConfig mode c) := by
  simp [Halted, readConfig, inputNodeCompositeMachine]

@[simp] theorem returnConfig_not_halted
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (returnConfig mode selected c) := by
  simp [Halted, returnConfig, inputNodeCompositeMachine]

theorem look_successors_active
    (c : Configuration InputIndexLookaheadState (Option Bool))
    (h : inputIndexLookaheadMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (lookConfig c) =
      [lookConfig (inputIndexLookaheadMachine.step c)] := by
  unfold NTM.successors
  simp only [lookConfig]
  rw [look_transition_active c.state c.tape.head h]
  simp [lookConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, inputIndexLookaheadMachine,
    Tape.write, Tape.move]

theorem read_successors_active
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool))
    (h : preservingReadMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (readConfig mode c) =
      [readConfig mode (preservingReadMachine.step c)] := by
  unfold NTM.successors
  simp only [readConfig]
  rw [read_transition_active mode c.state c.tape.head h]
  simp [readConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, preservingReadMachine,
    Tape.write, Tape.move]

theorem return_successors_active
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool))
    (h : inputAfterReadReturnMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (returnConfig mode selected c) =
      [returnConfig mode selected (inputAfterReadReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [returnConfig]
  rw [return_transition_active mode selected c.state c.tape.head h]
  simp [returnConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, inputAfterReadReturnMachine,
    Tape.write, Tape.move]

/-- The lookahead phase's deterministic configuration after fuel `n` is
reachable in the composite in at most `n` steps.  If the source TM halts
early, the witness uses that earlier time instead of requiring minimal fuel. -/
theorem look_run_reachable :
    ∀ (n : Nat)
      (c : Configuration InputIndexLookaheadState (Option Bool)),
      ∃ m ≤ n,
        lookConfig (inputIndexLookaheadMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m [lookConfig c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change lookConfig c ∈ [lookConfig c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : inputIndexLookaheadMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              inputIndexLookaheadMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            lookConfig (inputIndexLookaheadMachine.run (n + 1) c) ∈
              [lookConfig c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ :=
            ih (inputIndexLookaheadMachine.step c)
          have hsucc :
              lookConfig (inputIndexLookaheadMachine.step c) ∈
                inputNodeCompositeMachine.successors (lookConfig c) := by
            rw [look_successors_active c hhalt]
            simp
          have hone :
              lookConfig (inputIndexLookaheadMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1 [lookConfig c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [lookConfig c]
              (lookConfig c)
              (lookConfig (inputIndexLookaheadMachine.step c))
              (by simp [NTM.runBranches])
              (lookConfig_not_halted c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [lookConfig c]
              (lookConfig (inputIndexLookaheadMachine.step c))
              (lookConfig
                (inputIndexLookaheadMachine.run n
                  (inputIndexLookaheadMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem read_run_reachable
    (mode : InputReturnMode) :
    ∀ (n : Nat)
      (c : Configuration PreservingReadState (Option Bool)),
      ∃ m ≤ n,
        readConfig mode (preservingReadMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m [readConfig mode c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change readConfig mode c ∈ [readConfig mode c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : preservingReadMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              preservingReadMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            readConfig mode (preservingReadMachine.run (n + 1) c) ∈
              [readConfig mode c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (preservingReadMachine.step c)
          have hsucc :
              readConfig mode (preservingReadMachine.step c) ∈
                inputNodeCompositeMachine.successors (readConfig mode c) := by
            rw [read_successors_active mode c hhalt]
            simp
          have hone :
              readConfig mode (preservingReadMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1 [readConfig mode c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [readConfig mode c]
              (readConfig mode c)
              (readConfig mode (preservingReadMachine.step c))
              (by simp [NTM.runBranches])
              (readConfig_not_halted mode c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [readConfig mode c]
              (readConfig mode (preservingReadMachine.step c))
              (readConfig mode
                (preservingReadMachine.run n
                  (preservingReadMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem return_run_reachable
    (mode : InputReturnMode) (selected : Bool) :
    ∀ (n : Nat)
      (c : Configuration InputAfterReadReturnState (Option Bool)),
      ∃ m ≤ n,
        returnConfig mode selected (inputAfterReadReturnMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m
            [returnConfig mode selected c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change returnConfig mode selected c ∈ [returnConfig mode selected c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : inputAfterReadReturnMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              inputAfterReadReturnMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            returnConfig mode selected
                (inputAfterReadReturnMachine.run (n + 1) c) ∈
              [returnConfig mode selected c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ :=
            ih (inputAfterReadReturnMachine.step c)
          have hsucc :
              returnConfig mode selected
                  (inputAfterReadReturnMachine.step c) ∈
                inputNodeCompositeMachine.successors
                  (returnConfig mode selected c) := by
            rw [return_successors_active mode selected c hhalt]
            simp
          have hone :
              returnConfig mode selected
                  (inputAfterReadReturnMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1
                  [returnConfig mode selected c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [returnConfig mode selected c]
              (returnConfig mode selected c)
              (returnConfig mode selected
                (inputAfterReadReturnMachine.step c))
              (by simp [NTM.runBranches])
              (returnConfig_not_halted mode selected c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [returnConfig mode selected c]
              (returnConfig mode selected
                (inputAfterReadReturnMachine.step c))
              (returnConfig mode selected
                (inputAfterReadReturnMachine.run n
                  (inputAfterReadReturnMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

/-- Final control mode of the mode-aware input return. -/
def inputNodeFinalMode (tail frameStack : CanonicalFinalProof.BitString) : InputReturnMode :=
  match tail with
  | _ :: _ => .frameStack
  | [] =>
      match frameStack with
      | _ :: _ => .frameStack
      | [] => .done

/-- The canonical return target has the final mode encoded above. -/
theorem inputAfterReadTarget_eq_finalMode
    (witness tail frameStack : CanonicalFinalProof.BitString)
    (consumed padding : Nat) :
    inputAfterReadTarget witness consumed tail frameStack padding =
      { state := .halt (inputNodeFinalMode tail frameStack),
        tape :=
          (inputAfterReadTarget
            witness consumed tail frameStack padding).tape } := by
  cases tail with
  | cons b bs =>
      rfl
  | nil =>
      cases frameStack <;> rfl

/-- Total majorant for the fused input-node NTM:
lookahead + handoff + preserving read + handoff + return + handoff. -/
def inputNodeCompositeFuel
    (consumed i : Nat) (tail frameStack : CanonicalFinalProof.BitString) : Nat :=
  (2 * i + 6) + 1 +
    preservingReadGapFuel consumed i + 1 +
    P01InputNodeRoundTrip.inputAfterReadReturnFuel
      (consumedAfterInputIndex consumed i) tail frameStack + 1


/-- Explicit quadratic/linear envelope for the fused input-node route. -/
theorem inputNodeCompositeFuel_le
    (consumed i : Nat)
    (tail frameStack : CanonicalFinalProof.BitString) :
    inputNodeCompositeFuel consumed i tail frameStack ≤
      (2 * consumed + 4 * (i + 1) + 6) * i +
        4 * consumed + 8 * i + tail.length + frameStack.length + 30 := by
  unfold inputNodeCompositeFuel
  have hread := preservingReadGapFuel_le consumed i
  have hret :=
    inputAfterReadReturnFuel_le
      (consumedAfterInputIndex consumed i) tail frameStack
  unfold consumedAfterInputIndex at hret
  let P := (2 * consumed + 4 * (i + 1) + 6) * i
  have hreadP :
      preservingReadGapFuel consumed i ≤
        P + 3 * consumed + 5 * (i + 1) + 12 := by
    simpa [P] using hread
  change
    (2 * i + 6) + 1 +
        preservingReadGapFuel consumed i + 1 +
        P01InputNodeRoundTrip.inputAfterReadReturnFuel
          (consumed + i + 1) tail frameStack + 1 ≤
      P + 4 * consumed + 8 * i +
        tail.length + frameStack.length + 30
  omega

/-- Full physical input-node reachability in one fixed NTM.

Starting at the evaluator cursor on the unary index, the fused machine reaches
an accepting `.done` state carrying exactly the selected witness bit.  The
physical tape is exactly the canonical mode-aware return target. -/
theorem inputNodeComposite_reaches_done
    (witness tail frameStack : CanonicalFinalProof.BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputNodeCompositeFuel consumed i tail frameStack,
      ({ state :=
           .done (witness.getD i false)
             (inputNodeFinalMode tail frameStack),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex consumed i)
             tail frameStack padding).tape } :
        CompositeConfig) ∈
      inputNodeCompositeMachine.runBranches m
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (encodeNat i ++ tail) frameStack padding }] := by
  let mode := inputReturnModeOf tail frameStack
  let selected := witness.getD i false
  let consumed' := consumedAfterInputIndex consumed i
  let tape0 :=
    evalCursorReadTape witness consumed
      (encodeNat i ++ tail) frameStack padding

  let cLook0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := inputIndexLookaheadMachine.initial, tape := tape0 }
  let cLookH : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .halt mode, tape := tape0 }

  have hLookExact :
      inputIndexLookaheadMachine.run (2 * i + 6) cLook0 = cLookH := by
    dsimp [cLook0, cLookH, tape0, mode]
    exact lookahead_inputReturnMode
      witness tail frameStack consumed padding i

  obtain ⟨mL, hmL, hL⟩ :=
    look_run_reachable (2 * i + 6) cLook0
  have hLH :
      lookConfig cLookH ∈
        inputNodeCompositeMachine.runBranches mL [lookConfig cLook0] := by
    rw [hLookExact] at hL
    exact hL

  let cRead0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial, tape := tape0 }
  have hLookSucc :
      readConfig mode cRead0 ∈
        inputNodeCompositeMachine.successors (lookConfig cLookH) := by
    have hmem :
        ({ state := .read mode preservingReadMachine.initial, tape := tape0 } :
          CompositeConfig) ∈
        inputNodeCompositeMachine.successors
          ({ state := .look (.halt mode), tape := tape0 } : CompositeConfig) := by
      rw [look_handoff_successors]
      simp
    simpa [cLookH, cRead0, lookConfig, readConfig] using hmem

  have hReadStart :
      readConfig mode cRead0 ∈
        inputNodeCompositeMachine.runBranches (mL + 1) [lookConfig cLook0] := by
    exact mem_runBranches_succ_of_successor
      inputNodeCompositeMachine mL [lookConfig cLook0]
      (lookConfig cLookH) (readConfig mode cRead0)
      hLH (lookConfig_not_halted cLookH) hLookSucc

  let readFuel := preservingReadGapFuel consumed i
  obtain ⟨mR, hmR, hR⟩ :=
    read_run_reachable mode readFuel cRead0

  let cReadH : Configuration PreservingReadState (Option Bool) :=
    { state := .halt selected,
      tape :=
        afterIndexedReadTape witness consumed'
          tail frameStack padding }

  have hReadExact :
      preservingReadMachine.run readFuel cRead0 = cReadH := by
    dsimp [readFuel, cRead0, cReadH, selected, consumed', tape0]
    exact inputNode000_read_to_afterIndexedReadTape
      witness tail frameStack consumed padding i hi

  have hRH :
      readConfig mode cReadH ∈
        inputNodeCompositeMachine.runBranches mR [readConfig mode cRead0] := by
    rw [hReadExact] at hR
    exact hR

  have hReadReached :
      readConfig mode cReadH ∈
        inputNodeCompositeMachine.runBranches ((mL + 1) + mR)
          [lookConfig cLook0] :=
    mem_runBranches_trans inputNodeCompositeMachine
      (mL + 1) mR [lookConfig cLook0]
      (readConfig mode cRead0) (readConfig mode cReadH)
      hReadStart hRH

  let cRet0 : Configuration InputAfterReadReturnState (Option Bool) :=
    { state := .start mode,
      tape :=
        afterIndexedReadTape witness consumed'
          tail frameStack padding }

  have hReadSucc :
      returnConfig mode selected cRet0 ∈
        inputNodeCompositeMachine.successors (readConfig mode cReadH) := by
    have hmem :
        ({ state := .ret mode selected (.start mode),
           tape :=
             afterIndexedReadTape witness consumed'
               tail frameStack padding } : CompositeConfig) ∈
        inputNodeCompositeMachine.successors
          ({ state := .read mode (.halt selected),
             tape :=
               afterIndexedReadTape witness consumed'
                 tail frameStack padding } : CompositeConfig) := by
      rw [read_handoff_successors]
      simp
    simpa [cReadH, cRet0, readConfig, returnConfig] using hmem

  have hReturnStart :
      returnConfig mode selected cRet0 ∈
        inputNodeCompositeMachine.runBranches (((mL + 1) + mR) + 1)
          [lookConfig cLook0] := by
    exact mem_runBranches_succ_of_successor
      inputNodeCompositeMachine ((mL + 1) + mR) [lookConfig cLook0]
      (readConfig mode cReadH) (returnConfig mode selected cRet0)
      hReadReached (readConfig_not_halted mode cReadH) hReadSucc

  let retFuel :=
    P01InputNodeRoundTrip.inputAfterReadReturnFuel
      consumed' tail frameStack
  obtain ⟨mT, hmT, hT⟩ :=
    return_run_reachable mode selected retFuel cRet0

  let cRetH : Configuration InputAfterReadReturnState (Option Bool) :=
    { state := .halt (inputNodeFinalMode tail frameStack),
      tape :=
        (inputAfterReadTarget witness consumed'
          tail frameStack padding).tape }

  have hReturnExact :
      inputAfterReadReturnMachine.run retFuel cRet0 = cRetH := by
    dsimp [retFuel, cRet0, cRetH, mode, consumed']
    rw [inputNode000_afterRead_return
      witness tail frameStack
      (consumedAfterInputIndex consumed i) padding]
    exact inputAfterReadTarget_eq_finalMode
      witness tail frameStack
      (consumedAfterInputIndex consumed i) padding

  have hTH :
      returnConfig mode selected cRetH ∈
        inputNodeCompositeMachine.runBranches mT
          [returnConfig mode selected cRet0] := by
    rw [hReturnExact] at hT
    exact hT

  have hReturnReached :
      returnConfig mode selected cRetH ∈
        inputNodeCompositeMachine.runBranches
          ((((mL + 1) + mR) + 1) + mT)
          [lookConfig cLook0] :=
    mem_runBranches_trans inputNodeCompositeMachine
      (((mL + 1) + mR) + 1) mT [lookConfig cLook0]
      (returnConfig mode selected cRet0)
      (returnConfig mode selected cRetH)
      hReturnStart hTH

  let cDone : CompositeConfig :=
    { state := .done selected (inputNodeFinalMode tail frameStack),
      tape :=
        (inputAfterReadTarget witness consumed'
          tail frameStack padding).tape }

  have hReturnSucc :
      cDone ∈
        inputNodeCompositeMachine.successors
          (returnConfig mode selected cRetH) := by
    have hmem :
        ({ state := .done selected (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness consumed'
               tail frameStack padding).tape } : CompositeConfig) ∈
        inputNodeCompositeMachine.successors
          ({ state := .ret mode selected
              (.halt (inputNodeFinalMode tail frameStack)),
             tape :=
               (inputAfterReadTarget witness consumed'
                 tail frameStack padding).tape } : CompositeConfig) := by
      rw [return_handoff_successors]
      simp
    simpa [cRetH, cDone, returnConfig] using hmem

  have hDone :
      cDone ∈
        inputNodeCompositeMachine.runBranches
          (((((mL + 1) + mR) + 1) + mT) + 1)
          [lookConfig cLook0] := by
    exact mem_runBranches_succ_of_successor
      inputNodeCompositeMachine ((((mL + 1) + mR) + 1) + mT)
      [lookConfig cLook0]
      (returnConfig mode selected cRetH) cDone
      hReturnReached
      (returnConfig_not_halted mode selected cRetH)
      hReturnSucc

  refine ⟨(((((mL + 1) + mR) + 1) + mT) + 1), ?_, ?_⟩
  · have hsum :
        (((((mL + 1) + mR) + 1) + mT) + 1) ≤
          (((((2 * i + 6) + 1) + readFuel) + 1) + retFuel) + 1 := by
      omega
    simpa [inputNodeCompositeFuel, readFuel, retFuel, consumed'] using hsum
  · dsimp [cDone, selected, consumed', cLook0, tape0] at hDone ⊢
    simpa [lookConfig, inputNodeCompositeMachine] using hDone

/-- The reached terminal configuration is accepting in the fused NTM. -/
theorem inputNodeComposite_reaches_accepting
    (witness tail frameStack : CanonicalFinalProof.BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputNodeCompositeFuel consumed i tail frameStack,
      ∃ c ∈ inputNodeCompositeMachine.runBranches m
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (encodeNat i ++ tail) frameStack padding }],
        inputNodeCompositeMachine.accepting c.state = true ∧
        (∃ mode, c.state = .done (witness.getD i false) mode) := by
  obtain ⟨m, hm, hmem⟩ :=
    inputNodeComposite_reaches_done
      witness tail frameStack consumed padding i hi
  refine ⟨m, hm, _, hmem, ?_, ?_⟩
  · rfl
  · exact ⟨inputNodeFinalMode tail frameStack, rfl⟩


/-- The accepting terminal reached by the fused input-node machine persists to
the uniform composite fuel, giving an exact `AcceptsWithin` certificate for
the physical input primitive.  This acceptance is an internal phase handoff
signal; the selected Boolean remains carried in the `.done` control state. -/
theorem inputNodeComposite_acceptsWithin
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    inputNodeCompositeMachine.AcceptsWithin
      (inputNodeCompositeFuel consumed i tail frameStack)
      { state := inputNodeCompositeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } := by
  obtain ⟨m, hm, c, hc, hacc, _hselected⟩ :=
    inputNodeComposite_reaches_accepting
      witness tail frameStack consumed padding i hi
  have hhalt : Halted inputNodeCompositeMachine c :=
    halted_of_accepting inputNodeCompositeMachine c hacc
  have hpersist :=
    mem_runBranches_persist inputNodeCompositeMachine
      m (inputNodeCompositeFuel consumed i tail frameStack - m)
      [{ state := inputNodeCompositeMachine.initial,
         tape :=
           evalCursorReadTape witness consumed
             (encodeNat i ++ tail) frameStack padding }]
      c hc hhalt
  have hsum :
      m + (inputNodeCompositeFuel consumed i tail frameStack - m) =
        inputNodeCompositeFuel consumed i tail frameStack := by
    omega
  rw [hsum] at hpersist
  exact ⟨c, hpersist, hacc⟩


/-- Operational determinism lifts from one-step successors to every finite run
started from a singleton configuration. -/
theorem inputNodeComposite_runBranches_length_le_one :
    ∀ (n : Nat) (c : CompositeConfig),
      (inputNodeCompositeMachine.runBranches n [c]).length ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [NTM.runBranches]
  | succ n ih =>
      intro c
      by_cases hh : Halted inputNodeCompositeMachine c
      · rw [runBranches_singleton_halted inputNodeCompositeMachine (n + 1) c hh]
        simp
      · rw [runBranches_singleton_active inputNodeCompositeMachine n c hh]
        have hlen :=
          inputNodeComposite_successors_length_le_one c
        cases hs : inputNodeCompositeMachine.successors c with
        | nil =>
            simp [hs, runBranches_nil]
        | cons d ds =>
            cases ds with
            | nil =>
                simpa [hs] using ih d
            | cons e es =>
                simp [hs] at hlen

/-- A list of length at most one containing `x` is exactly the singleton
`[x]`. -/
theorem list_eq_singleton_of_mem_length_le_one
    {α : Type} (x : α) (xs : List α)
    (hx : x ∈ xs) (hlen : xs.length ≤ 1) :
    xs = [x] := by
  cases xs with
  | nil =>
      simp at hx
  | cons y ys =>
      cases ys with
      | nil =>
          simp only [List.mem_singleton] at hx
          subst y
          rfl
      | cons z zs =>
          simp at hlen

/-- The fused input-node primitive is terminal at the same uniform fuel used
by its acceptance certificate.  No branch can remain active because the
machine is operationally deterministic and an accepting terminal is present
at that fuel. -/
theorem inputNodeComposite_haltsWithin
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    inputNodeCompositeMachine.HaltsWithin
      (inputNodeCompositeFuel consumed i tail frameStack)
      { state := inputNodeCompositeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } := by
  let start : CompositeConfig :=
    { state := inputNodeCompositeMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (encodeNat i ++ tail) frameStack padding }
  obtain ⟨terminal, hmem, hacc⟩ :=
    inputNodeComposite_acceptsWithin
      witness tail frameStack consumed padding i hi
  have hlen :
      (inputNodeCompositeMachine.runBranches
        (inputNodeCompositeFuel consumed i tail frameStack) [start]).length ≤ 1 :=
    inputNodeComposite_runBranches_length_le_one
      (inputNodeCompositeFuel consumed i tail frameStack) start
  have hmem' :
      terminal ∈
        inputNodeCompositeMachine.runBranches
          (inputNodeCompositeFuel consumed i tail frameStack) [start] := by
    simpa [start] using hmem
  have heq :
      inputNodeCompositeMachine.runBranches
          (inputNodeCompositeFuel consumed i tail frameStack) [start] =
        [terminal] :=
    list_eq_singleton_of_mem_length_le_one terminal _ hmem' hlen
  rw [haltsWithin_iff_halted]
  intro z hz
  rw [heq] at hz
  simp only [List.mem_singleton] at hz
  subst z
  exact halted_of_accepting inputNodeCompositeMachine terminal hacc


/-- An unterminated unary index is rejected by the full input-node composite.

The lookahead scans all true markers, reaches its nested reject state on the
blank where the false terminator was required, and the fail-closed composite
wrapper promotes that nested state to the unique terminal reject. -/
theorem unterminated_index_reaches_reject
    (witness frameStack : BitString)
    (consumed padding n : Nat) :
    ∃ m ≤ n + 2, ∃ tape : Tape (Option Bool),
      ({ state := InputNodeCompositeState.reject, tape := tape } :
        CompositeConfig) ∈
      inputNodeCompositeMachine.runBranches m
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (List.replicate n true) frameStack padding }] := by
  let c0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := inputIndexLookaheadMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (List.replicate n true) frameStack padding }
  let cR := inputIndexLookaheadMachine.run (n + 1) c0

  have hstate : cR.state = .reject := by
    dsimp [cR, c0]
    exact unterminated_true_index_rejects
      witness frameStack consumed padding n

  obtain ⟨m0, hm0, h0⟩ :=
    look_run_reachable (n + 1) c0

  let cLook : CompositeConfig := lookConfig cR
  have h0' :
      cLook ∈ inputNodeCompositeMachine.runBranches m0
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (List.replicate n true) frameStack padding }] := by
    simpa [cLook, cR, c0, lookConfig,
      inputNodeCompositeMachine] using h0

  let cReject : CompositeConfig :=
    { state := .reject, tape := cR.tape }
  have hsucc :
      cReject ∈ inputNodeCompositeMachine.successors cLook := by
    rcases cR with ⟨q, tape⟩
    simp only at hstate
    subst q
    rw [(nested_input_reject_successors (.sourceTail) false tape).1]
    simp [cLook, cReject, lookConfig]

  have hone :
      cReject ∈ inputNodeCompositeMachine.runBranches 1 [cLook] := by
    have h :=
      mem_runBranches_succ_of_successor
        inputNodeCompositeMachine 0 [cLook] cLook cReject
        (by simp [NTM.runBranches])
        (lookConfig_not_halted cR) hsucc
    simpa using h

  have hAll :=
    mem_runBranches_trans inputNodeCompositeMachine
      m0 1
      [{ state := inputNodeCompositeMachine.initial,
         tape :=
           evalCursorReadTape witness consumed
             (List.replicate n true) frameStack padding }]
      cLook cReject h0' hone

  refine ⟨m0 + 1, by omega, cR.tape, ?_⟩
  simpa [cReject] using hAll

#print axioms MCore.Real.P01InputNodeCompositeRun.unterminated_index_reaches_reject

#print axioms MCore.Real.P01InputNodeCompositeRun.inputAfterReadTarget_eq_finalMode
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeCompositeFuel_le
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeComposite_reaches_done
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeComposite_reaches_accepting
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeComposite_acceptsWithin
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeComposite_runBranches_length_le_one
#print axioms MCore.Real.P01InputNodeCompositeRun.inputNodeComposite_haltsWithin


/-- A completed lookahead phase reaches the preserving-reader entry in exactly
one composite step. -/
theorem look_handoff_reachable
    (mode : InputReturnMode) (tape : Tape (Option Bool)) :
    { state := .read mode preservingReadMachine.initial, tape := tape } ∈
      inputNodeCompositeMachine.runBranches 1
        [{ state := .look (.halt mode), tape := tape }] := by
  have hact :
      ¬ Halted inputNodeCompositeMachine
        ({ state := .look (.halt mode), tape := tape } : CompositeConfig) := by
    simp [Halted, inputNodeCompositeMachine]
  have hsucc :
      ({ state := .read mode preservingReadMachine.initial, tape := tape } :
        CompositeConfig) ∈
      inputNodeCompositeMachine.successors
        { state := .look (.halt mode), tape := tape } := by
    rw [look_handoff_successors mode tape]
    simp
  have h :=
    mem_runBranches_succ_of_successor
      inputNodeCompositeMachine 0
      [({ state := .look (.halt mode), tape := tape } : CompositeConfig)]
      ({ state := .look (.halt mode), tape := tape } : CompositeConfig)
      ({ state := .read mode preservingReadMachine.initial, tape := tape } :
        CompositeConfig)
      (by simp [NTM.runBranches]) hact hsucc
  simpa using h

/-- A completed read reaches the mode-aware return entry in exactly one
composite step. -/
theorem read_handoff_reachable
    (mode : InputReturnMode) (selected : Bool)
    (tape : Tape (Option Bool)) :
    { state := .ret mode selected (.start mode), tape := tape } ∈
      inputNodeCompositeMachine.runBranches 1
        [{ state := .read mode (.halt selected), tape := tape }] := by
  have hact :
      ¬ Halted inputNodeCompositeMachine
        ({ state := .read mode (.halt selected), tape := tape } :
          CompositeConfig) := by
    simp [Halted, inputNodeCompositeMachine]
  have hsucc :
      ({ state := .ret mode selected (.start mode), tape := tape } :
        CompositeConfig) ∈
      inputNodeCompositeMachine.successors
        { state := .read mode (.halt selected), tape := tape } := by
    rw [read_handoff_successors mode selected tape]
    simp
  have h :=
    mem_runBranches_succ_of_successor
      inputNodeCompositeMachine 0
      [({ state := .read mode (.halt selected), tape := tape } :
        CompositeConfig)]
      ({ state := .read mode (.halt selected), tape := tape } :
        CompositeConfig)
      ({ state := .ret mode selected (.start mode), tape := tape } :
        CompositeConfig)
      (by simp [NTM.runBranches]) hact hsucc
  simpa using h

/-- A completed return reaches the globally accepting input-node state in
exactly one composite step. -/
theorem return_handoff_reachable
    (mode finalMode : InputReturnMode) (selected : Bool)
    (tape : Tape (Option Bool)) :
    { state := .done selected finalMode, tape := tape } ∈
      inputNodeCompositeMachine.runBranches 1
        [{ state := .ret mode selected (.halt finalMode), tape := tape }] := by
  have hact :
      ¬ Halted inputNodeCompositeMachine
        ({ state := .ret mode selected (.halt finalMode), tape := tape } :
          CompositeConfig) := by
    simp [Halted, inputNodeCompositeMachine]
  have hsucc :
      ({ state := .done selected finalMode, tape := tape } : CompositeConfig) ∈
      inputNodeCompositeMachine.successors
        { state := .ret mode selected (.halt finalMode), tape := tape } := by
    rw [return_handoff_successors mode finalMode selected tape]
    simp
  have h :=
    mem_runBranches_succ_of_successor
      inputNodeCompositeMachine 0
      [({ state := .ret mode selected (.halt finalMode), tape := tape } :
        CompositeConfig)]
      ({ state := .ret mode selected (.halt finalMode), tape := tape } :
        CompositeConfig)
      ({ state := .done selected finalMode, tape := tape } : CompositeConfig)
      (by simp [NTM.runBranches]) hact hsucc
  simpa using h

#print axioms MCore.Real.P01InputNodeCompositeRun.look_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.read_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.return_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.look_run_reachable
#print axioms MCore.Real.P01InputNodeCompositeRun.read_run_reachable
#print axioms MCore.Real.P01InputNodeCompositeRun.return_run_reachable

end P01InputNodeCompositeRun
end Real
end MCore
