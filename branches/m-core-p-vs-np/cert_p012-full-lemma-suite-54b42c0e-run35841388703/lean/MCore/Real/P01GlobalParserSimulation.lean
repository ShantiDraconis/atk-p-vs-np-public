import MCore.Real.CanonicalSATParserBinaryHeadProof
import MCore.Real.CanonicalSATParserGlobalSpec
import MCore.Real.CanonicalSATRecursiveParserSimulation

namespace MCore
namespace Real
namespace P01GlobalParserSimulation

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog
open MachineRunLemmas

/-- Equality of finite right-tape representations modulo finitely many
explicit trailing blank cells. Internal blanks are preserved. -/
def RightBlankEq
    (a b : List (Option Bool)) : Prop :=
  ∃ (core : List (Option Bool)) (ka kb : Nat),
    a = core ++ List.replicate ka none ∧
    b = core ++ List.replicate kb none

theorem rightBlankEq_refl
    (a : List (Option Bool)) :
    RightBlankEq a a := by
  exact ⟨a, 0, 0, by simp, by simp⟩

theorem rightBlankEq_symm
    {a b : List (Option Bool)}
    (h : RightBlankEq a b) :
    RightBlankEq b a := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  exact ⟨core, kb, ka, hb, ha⟩

theorem rightBlankEq_cons
    (x : Option Bool)
    {a b : List (Option Bool)}
    (h : RightBlankEq a b) :
    RightBlankEq (x :: a) (x :: b) := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  refine ⟨x :: core, ka, kb, ?_, ?_⟩
  · simp [ha]
  · simp [hb]

theorem rightBlankEq_replicate
    (ka kb : Nat) :
    RightBlankEq
      (List.replicate ka (none : Option Bool))
      (List.replicate kb (none : Option Bool)) := by
  exact ⟨[], ka, kb, by simp, by simp⟩

/-- Configurations represent the same parser tape modulo explicit blank
padding at the far right. -/
def ConfigRightBlankEq
    (c d : Configuration (Fin 25) (Option Bool)) : Prop :=
  c.state = d.state ∧
  c.tape.left = d.tape.left ∧
  c.tape.head = d.tape.head ∧
  RightBlankEq c.tape.right d.tape.right

theorem configRightBlankEq_refl
    (c : Configuration (Fin 25) (Option Bool)) :
    ConfigRightBlankEq c c := by
  exact ⟨rfl, rfl, rfl, rightBlankEq_refl _⟩

theorem configRightBlankEq_symm
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq d c := by
  rcases h with ⟨hs, hl, hh, hr⟩
  exact ⟨hs.symm, hl.symm, hh.symm, rightBlankEq_symm hr⟩

private theorem move_stay_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .stay
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .stay
          { left := left, head := head, right := rb } } := by
  exact ⟨rfl, rfl, rfl, h⟩

private theorem move_left_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .left
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .left
          { left := left, head := head, right := rb } } := by
  cases left with
  | nil =>
      exact ⟨rfl, rfl, rfl, rightBlankEq_cons head h⟩
  | cons x xs =>
      exact ⟨rfl, rfl, rfl, rightBlankEq_cons head h⟩

private theorem move_right_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .right
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .right
          { left := left, head := head, right := rb } } := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  rw [ha, hb]
  cases core with
  | nil =>
      simp only [List.nil_append]
      cases ka with
      | zero =>
          cases kb with
          | zero =>
              exact ⟨rfl, rfl, rfl, rightBlankEq_refl []⟩
          | succ kb =>
              simp only [List.replicate_zero, List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate 0 kb⟩
      | succ ka =>
          cases kb with
          | zero =>
              simp only [List.replicate_zero, List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate ka 0⟩
          | succ kb =>
              simp only [List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate ka kb⟩
  | cons x xs =>
      simp only [List.cons_append, Tape.move]
      refine ⟨rfl, rfl, rfl, ?_⟩
      exact ⟨xs, ka, kb, rfl, rfl⟩

private theorem move_preserves
    (q : Fin 25)
    (dir : Direction)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none dir
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none dir
          { left := left, head := head, right := rb } } := by
  cases dir with
  | left => exact move_left_preserves q h
  | stay => exact move_stay_preserves q h
  | right => exact move_right_preserves q h

/-- The concrete parser transition is insensitive to explicit blank padding
beyond the represented right-hand tape contents. -/
theorem parser_step_respects_right_blank
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq
      (parserMachine.step c)
      (parserMachine.step d) := by
  rcases c with ⟨cs, ct⟩
  rcases ct with ⟨cl, ch, cr⟩
  rcases d with ⟨ds, dt⟩
  rcases dt with ⟨dl, dh, dr⟩
  rcases h with ⟨hs, hl, hh, hr⟩
  change cs = ds at hs
  change cl = dl at hl
  change ch = dh at hh
  change RightBlankEq cr dr at hr
  subst ds
  subst dl
  subst dh
  rcases htrans :
      parserMachine.transition cs ch with
      ⟨nextState, nextSymbol, dir⟩
  unfold TM.step
  rw [htrans]
  simp only [Tape.write, parserMachine_blank_none]
  exact move_preserves nextState dir hr

/-- Right-blank equivalence is a bisimulation for every bounded parser run. -/
theorem parser_run_respects_right_blank
    (fuel : Nat)
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq
      (parserMachine.run fuel c)
      (parserMachine.run fuel d) := by
  induction fuel generalizing c d with
  | zero =>
      exact h
  | succ fuel ih =>
      have hs := h.1
      have hhalt :
          parserMachine.halting c.state =
            parserMachine.halting d.state := by
        rw [hs]
      by_cases hc : parserMachine.halting c.state = true
      · have hd : parserMachine.halting d.state = true := by
          rw [← hhalt]
          exact hc
        simp only [TM.run, hc, hd, if_true]
        exact h
      · have hcf : parserMachine.halting c.state = false := by
          cases hq : parserMachine.halting c.state <;> simp_all
        have hdf : parserMachine.halting d.state = false := by
          rw [← hhalt]
          exact hcf
        simp only [TM.run, hcf, hdf, Bool.false_eq_true, if_false]
        exact ih (parser_step_respects_right_blank h)

theorem parser_run_state_eq_of_right_blank
    (fuel : Nat)
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    (parserMachine.run fuel c).state =
      (parserMachine.run fuel d).state :=
  (parser_run_respects_right_blank fuel h).1

/-- Successful head parsing strictly shortens the unread source. -/
theorem parseHead_rest_length_lt
    {bits : BitString}
    {head : Head}
    {rest : BitString}
    (hparse : parseHead bits = some (head, rest)) :
    rest.length < bits.length := by
  have hshape := parseHead_inverse bits head rest hparse
  cases head with
  | input i =>
      rw [hshape]
      simp [Head.encode]
      omega
  | const b =>
      rw [hshape]
      cases b <;> simp [Head.encode] <;> omega
  | not =>
      rw [hshape]
      simp [Head.encode]
      omega
  | and =>
      rw [hshape]
      simp [Head.encode]
      omega
  | or =>
      rw [hshape]
      simp [Head.encode]
      omega

/-- Once fuel is at least one more than the unread source length,
extra abstract parser fuel is semantically irrelevant.  This lets the physical
global induction recurse with the residual fuel left by a consumed head while
comparing against the canonical `bits.length + 1` specification. -/
theorem logParseCore_fuel_stable
    (bits : BitString)
    (log : SlotLog)
    (m n : Nat)
    (hm : bits.length + 1 ≤ m)
    (hn : bits.length + 1 ≤ n) :
    CanonicalSATParserGlobalSpec.logParseCore m log bits =
      CanonicalSATParserGlobalSpec.logParseCore n log bits := by
  induction m generalizing n log bits with
  | zero =>
      omega
  | succ m ih =>
      cases n with
      | zero =>
          omega
      | succ n =>
          by_cases hactive : activeSlots log = 0
          · simp [CanonicalSATParserGlobalSpec.logParseCore, hactive]
          · cases hparse : parseHead bits with
            | none =>
                simp [CanonicalSATParserGlobalSpec.logParseCore,
                  hactive, hparse]
            | some p =>
                rcases p with ⟨head, rest⟩
                have hlt : rest.length < bits.length :=
                  parseHead_rest_length_lt hparse
                have hm' : rest.length + 1 ≤ m := by
                  omega
                have hn' : rest.length + 1 ≤ n := by
                  omega
                cases head with
                | input i =>
                    cases hpop : popSlot log with
                    | none =>
                        simp [CanonicalSATParserGlobalSpec.logParseCore,
                          hactive, hparse, hpop]
                    | some log' =>
                        simpa [CanonicalSATParserGlobalSpec.logParseCore,
                          hactive, hparse, hpop] using
                          ih rest log' n hm' hn'
                | const b =>
                    cases hpop : popSlot log with
                    | none =>
                        simp [CanonicalSATParserGlobalSpec.logParseCore,
                          hactive, hparse, hpop]
                    | some log' =>
                        simpa [CanonicalSATParserGlobalSpec.logParseCore,
                          hactive, hparse, hpop] using
                          ih rest log' n hm' hn'
                | not =>
                    simpa [CanonicalSATParserGlobalSpec.logParseCore,
                      hactive, hparse] using
                      ih rest log n hm' hn'
                | and =>
                    simpa [CanonicalSATParserGlobalSpec.logParseCore,
                      hactive, hparse] using
                      ih rest (pushSlot log) n hm' hn'
                | or =>
                    simpa [CanonicalSATParserGlobalSpec.logParseCore,
                      hactive, hparse] using
                      ih rest (pushSlot log) n hm' hn'

#print axioms MCore.Real.P01GlobalParserSimulation.logParseCore_fuel_stable

theorem activeSlots_reverse
    (log : SlotLog) :
    activeSlots log.reverse = activeSlots log := by
  induction log with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, activeSlots_append, ih]
      cases b <;> simp [activeSlots, Nat.add_comm]

theorem rightBlankEq_append_none
    (right : List (Option Bool)) :
    RightBlankEq (right ++ [none]) right := by
  exact ⟨right, 1, 0, by simp, by simp⟩

/-- State-16/17 source checks differing only by one explicit far-right blank
represent the same infinite blank tape. -/
theorem leafSourceCheck_trailing_blank
    (q : Fin 25)
    (sourceLeft right : List (Option Bool)) :
    ConfigRightBlankEq
      (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        q sourceLeft (right ++ [none]))
      (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        q sourceLeft right) := by
  unfold CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
  cases sourceLeft with
  | nil =>
      exact ⟨rfl, rfl, rfl,
        rightBlankEq_cons none (rightBlankEq_append_none right)⟩
  | cons x xs =>
      exact ⟨rfl, rfl, rfl,
        rightBlankEq_cons none (rightBlankEq_append_none right)⟩

private theorem map_some_false_suffix
    (suffix : SlotLog)
    (hall : ∀ b ∈ suffix, b = false) :
    suffix.map some =
      List.replicate suffix.length (some false) := by
  have hs :=
    CanonicalSATParserLeafPopProof.all_false_eq_replicate suffix hall
  rw [hs]
  simp

/-- Complete the physical leaf pop and older-active-slot scan.  The exact
output differs from the canonical source-check configuration only by the
explicit far-right blank exposed by scanning to the end of the work region. -/
theorem leaf_afterEnd_active_to_source
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ k : Nat,
      parserMachine.run k
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hpre : activeSlots pre ≠ 0 := by
    intro hz
    apply hactive
    rw [hlog', activeSlots_append]
    simp [activeSlots, hz, hszero]
  have hpreRev : activeSlots pre.reverse ≠ 0 := by
    simpa [activeSlots_reverse] using hpre
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  refine ⟨(suffix.length + 1) + (pre.length + 1), ?_⟩
  rw [MachineRunLemmas.run_add]
  rw [hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_active_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRev
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (17 : Fin 25) sourceLeft)
        hright

/-- Same leaf pop path when no active slot remains. -/
theorem leaf_afterEnd_inactive_to_source
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ k : Nat,
      parserMachine.run k
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          16 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hprezero : activeSlots pre = 0 := by
    rw [hlog', activeSlots_append] at hzero
    simpa [activeSlots, hszero] using hzero
  have hpreall : ∀ b ∈ pre, b = false :=
    (activeSlots_eq_zero_iff_all_false pre).mp hprezero
  have hpreRevAll : ∀ b ∈ pre.reverse, b = false := by
    intro b hb
    exact hpreall b (by simpa using hb)
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  refine ⟨(suffix.length + 1) + (pre.length + 1), ?_⟩
  rw [MachineRunLemmas.run_add]
  rw [hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_all_false_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRevAll
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (16 : Fin 25) sourceLeft)
        hright

/-- A physical rightmost-slot pop changes only a bit, never the work-log
length. -/
theorem popSlot_length
    {log log' : SlotLog}
    (hpop : popSlot log = some log') :
    log'.length = log.length := by
  induction log generalizing log' with
  | nil =>
      simp [popSlot] at hpop
  | cons b bs ih =>
      cases hbs : popSlot bs with
      | some bs' =>
          simp [popSlot, hbs] at hpop
          subst log'
          simp [ih hbs]
      | none =>
          cases b with
          | false =>
              simp [popSlot, hbs] at hpop
          | true =>
              simp [popSlot, hbs] at hpop
              subst log'
              rfl

/-- Positive abstract slot count guarantees a physical pop witness. -/
theorem popSlot_exists_of_active
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0) :
    ∃ log', popSlot log = some log' := by
  cases h : popSlot log with
  | none =>
      exact False.elim (hactive ((popSlot_none_iff log).mp h))
  | some log' =>
      refine ⟨log', ?_⟩
      simpa using h


/-- Complete an active leaf return through the certified source rewind.
The physical source-check carries one explicit far-right blank; the blank-tape
bisimulation transports it to the canonical source-check theorem. -/
theorem leaf_afterEnd_roundtrip_nonempty_active
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ steps : Nat,
      ConfigRightBlankEq
        (parserMachine.run steps
          (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
            (none :: some last ::
              (rest.map some ++
                List.replicate pad (none : Option Bool)))
            log none))
        (phaseConfig 4 pad (rest.reverse ++ [last]) log') := by
  let sourceLeft : List (Option Bool) :=
    some last ::
      (rest.map some ++ List.replicate pad (none : Option Bool))
  rcases leaf_afterEnd_active_to_source sourceLeft log log' hpop hactive with
    ⟨k, hk⟩
  refine ⟨k + (rest.length + 2), ?_⟩
  rw [MachineRunLemmas.run_add, hk]
  have hcfg :=
    leafSourceCheck_trailing_blank
      (17 : Fin 25) sourceLeft (log'.map some)
  have hrun :=
    parser_run_respects_right_blank (rest.length + 2) hcfg
  have hcanon :=
    CanonicalSATParserLeafSourceProof.leaf17_roundtrip_to_phase
      pad hpad last rest log'
  have hcanon' :
      parserMachine.run (rest.length + 2)
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some)) =
        phaseConfig 4 pad (rest.reverse ++ [last]) log' := by
    simpa [sourceLeft] using hcanon
  rw [hcanon'] at hrun
  exact hrun


/-- Every nonempty bitstring has the source shape used by the certified
right-to-left source-return lemmas. -/
theorem nonempty_eq_reverse_append_last
    (bits : BitString)
    (hne : bits ≠ []) :
    ∃ rest : BitString, ∃ last : Bool,
      bits = rest.reverse ++ [last] := by
  cases hrev : bits.reverse with
  | nil =>
      have : bits = [] := by
        simpa using congrArg List.reverse hrev
      exact False.elim (hne this)
  | cons last rest =>
      refine ⟨rest, last, ?_⟩
      have h := congrArg List.reverse hrev
      simpa [List.reverse_cons] using h

/-- If a leaf consumes the final active slot exactly when source is exhausted,
the concrete parser reaches its canonical accepting state. -/
theorem leaf_afterEnd_inactive_exhausted_accepts
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ steps : Nat, ∃ right : List (Option Bool),
      parserMachine.run steps
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafSourceProof.leafAcceptConfig pad right := by
  rcases leaf_afterEnd_inactive_to_source
      (List.replicate pad (none : Option Bool))
      log log' hpop hzero with
    ⟨k, hk⟩
  let right := log'.map some ++ [none]
  refine ⟨k + 1, right, ?_⟩
  rw [MachineRunLemmas.run_add, hk]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf16_exhausted_accepts
      pad hpad right
  simpa [TM.run] using hstep

/-- If the final active slot is consumed while unread source remains, the
concrete parser reaches the canonical rejecting state. -/
theorem leaf_afterEnd_inactive_residual_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ steps : Nat, ∃ cfg : Configuration (Fin 25) (Option Bool),
      parserMachine.run steps
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: tail.reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none) = cfg ∧
      parserMachine.halting cfg.state = true ∧
      parserAccepting cfg.state = false := by
  rcases nonempty_eq_reverse_append_last tail htail with
    ⟨rest, last, htailShape⟩
  subst tail
  have hrev :
      (rest.reverse ++ [last]).reverse.map some =
        some last :: rest.map some := by
    simp [List.map_append]
  rcases leaf_afterEnd_inactive_to_source
      (some last ::
        (rest.map some ++ List.replicate pad (none : Option Bool)))
      log log' hpop hzero with
    ⟨k, hk⟩
  let right := log'.map some ++ [none]
  let cfg :=
    CanonicalSATParserTerminalBranches.leafResidualRejectConfig
      pad last rest right
  refine ⟨k + 1, cfg, ?_, ?_, ?_⟩
  · rw [MachineRunLemmas.run_add]
    have hstart :
        CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: (rest.reverse ++ [last]).reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none =
        CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          log none := by
      simp [hrev, List.append_assoc]
    rw [hstart, hk]
    have hstep :=
      CanonicalSATParserTerminalBranches.leaf16_residual_rejects
        pad last rest right
    simpa [TM.run, cfg] using hstep
  · exact
      CanonicalSATParserTerminalBranches.leafResidualRejectConfig_halted
        pad last rest right
  · simp [cfg, CanonicalSATParserTerminalBranches.leafResidualRejectConfig,
      parserAccepting]

/-- If unread source is exhausted but an older active slot remains after a
leaf pop, the parser rejects because a required subtree is missing. -/
theorem leaf_afterEnd_active_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ steps : Nat, ∃ right : List (Option Bool),
      parserMachine.run steps
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafSourceProof.leafRejectConfig pad right := by
  rcases leaf_afterEnd_active_to_source
      (List.replicate pad (none : Option Bool))
      log log' hpop hactive with
    ⟨k, hk⟩
  let right := log'.map some ++ [none]
  refine ⟨k + 1, right, ?_⟩
  rw [MachineRunLemmas.run_add, hk]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf17_exhausted_rejects
      pad hpad right
  simpa [TM.run] using hstep


/-- A failed unary natural-number decode means that the payload contains only
true bits and never reaches its required false terminator. -/
theorem decodeNat_none_eq_replicate_true
    (bits : BitString)
    (h : CanonicalCircuitBits.decodeNat bits = none) :
    bits = List.replicate bits.length true := by
  induction bits with
  | nil =>
      rfl
  | cons b bs ih =>
      cases b with
      | false =>
          simp [CanonicalCircuitBits.decodeNat] at h
      | true =>
          cases htail : CanonicalCircuitBits.decodeNat bs with
          | none =>
              have hrec := ih htail
              rw [hrec]
              simp [List.replicate_succ]
          | some p =>
              simp [CanonicalCircuitBits.decodeNat, htail] at h

/-- State 10 rejects a unary INPUT payload that consists only of true bits and
therefore never supplies the mandatory false terminator. -/
theorem q10_true_payload_rejects
    (pad n : Nat)
    (log : SlotLog) :
    parserMachine.run (n + 1)
        (phaseConfig 10 pad (List.replicate n true) log) =
      phaseConfig 24 (pad + n) [] log := by
  induction n generalizing pad with
  | zero =>
      rw [show 0 + 1 = 1 by rfl]
      rw [TM.run, phaseConfig_state,
        CanonicalSATParserHeadProof.not_halted_10]
      change parserMachine.run 0
          (parserMachine.step
            (phaseConfig 10 pad [] log)) =
        phaseConfig 24 pad [] log
      rfl
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      simp only [List.replicate_succ]
      rw [TM.run, phaseConfig_state,
        CanonicalSATParserHeadProof.not_halted_10]
      have hstep :
          parserMachine.step
              (phaseConfig 10 pad
                (true :: List.replicate n true) log) =
            phaseConfig 10 (pad + 1)
              (List.replicate n true) log := by
        exact CanonicalSATParserHeadProof.step_erase_right
          10 10 pad true (List.replicate n true) log rfl
      rw [hstep]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (pad + 1)

/-- If parseHead fails at TAG_0, the concrete finite-control parser reaches the
canonical reject state 24. -/
theorem phase_parseHead_none_state_rejects
    (pad : Nat)
    (bits : BitString)
    (log : SlotLog)
    (hnone : parseHead bits = none) :
    ∃ steps : Nat,
      (parserMachine.run steps
        (phaseConfig 4 pad bits log)).state = (24 : Fin 25) := by
  cases bits with
  | nil =>
      refine ⟨1, ?_⟩
      simp [TM.run, phaseConfig, parserMachine, TM.step, Tape.write, Tape.move]
  | cons b1 r1 =>
      cases r1 with
      | nil =>
          cases b1
          · refine ⟨2, ?_⟩
            simp [TM.run, phaseConfig, parserMachine, TM.step,
              Tape.write, Tape.move]
          · refine ⟨2, ?_⟩
            simp [TM.run, phaseConfig, parserMachine, TM.step,
              Tape.write, Tape.move]
      | cons b2 r2 =>
          cases r2 with
          | nil =>
              cases b1 <;> cases b2
              · refine ⟨3, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨3, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨3, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨2, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
          | cons b3 rest =>
              cases b1 <;> cases b2 <;> cases b3
              · have hdec :
                    CanonicalCircuitBits.decodeNat rest = none := by
                  cases hd : CanonicalCircuitBits.decodeNat rest with
                  | none =>
                      rfl
                  | some p =>
                      rcases p with ⟨i, tail⟩
                      simp [parseHead, hd] at hnone
                have hrep :=
                  decodeNat_none_eq_replicate_true rest hdec
                rw [hrep]
                refine ⟨3 + (rest.length + 1), ?_⟩
                rw [MachineRunLemmas.run_add]
                rw [CanonicalSATParserHeadProof.tag_input_run]
                rw [q10_true_payload_rejects
                  (pad + 3) rest.length log]
                rfl
              · simp [parseHead] at hnone
              · simp [parseHead] at hnone
              · simp [parseHead] at hnone
              · simp [parseHead] at hnone
              · simp [parseHead] at hnone
              · refine ⟨2, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨2, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]

/-- Head-parser failure is therefore a genuine halted rejection, not merely a
state-level observation. -/
theorem phase_parseHead_none_rejects
    (pad : Nat)
    (bits : BitString)
    (log : SlotLog)
    (hnone : parseHead bits = none) :
    ∃ steps : Nat,
      parserMachine.halting
          (parserMachine.run steps
            (phaseConfig 4 pad bits log)).state = true ∧
      parserAccepting
          (parserMachine.run steps
            (phaseConfig 4 pad bits log)).state = false := by
  rcases phase_parseHead_none_state_rejects pad bits log hnone with
    ⟨steps, hstate⟩
  refine ⟨steps, ?_, ?_⟩
  · rw [hstate]
    decide
  · rw [hstate]
    decide


/-- Reparameterize the certified AND roundtrip over an arbitrary nonempty
unread suffix. -/
theorem and_head_roundtrip_any_nonempty
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log : SlotLog) :
    ∃ steps : Nat,
      parserMachine.run steps
          (phaseConfig 4 pad (Head.encode .and ++ tail) log) =
        phaseConfig 4
          (pad + (Head.encode .and).length)
          tail (pushSlot log) := by
  rcases nonempty_eq_reverse_append_last tail htail with
    ⟨rest, last, hshape⟩
  subst tail
  refine ⟨
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        Head.and (rest.reverse ++ [last]).length log.length +
      (log.length + 2 + (rest.length + 1)),
    ?_⟩
  exact CanonicalSATParserBinaryHeadProof.and_head_roundtrip_nonempty
    pad hpad last rest log

/-- Reparameterize the certified OR roundtrip over an arbitrary nonempty
unread suffix. -/
theorem or_head_roundtrip_any_nonempty
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log : SlotLog) :
    ∃ steps : Nat,
      parserMachine.run steps
          (phaseConfig 4 pad (Head.encode .or ++ tail) log) =
        phaseConfig 4
          (pad + (Head.encode .or).length)
          tail (pushSlot log) := by
  rcases nonempty_eq_reverse_append_last tail htail with
    ⟨rest, last, hshape⟩
  subst tail
  refine ⟨
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        Head.or (rest.reverse ++ [last]).length log.length +
      (log.length + 2 + (rest.length + 1)),
    ?_⟩
  exact CanonicalSATParserBinaryHeadProof.or_head_roundtrip_nonempty
    pad hpad last rest log

/-- Reparameterize the leaf active-slot roundtrip over any nonempty unread
suffix. -/
theorem leaf_afterEnd_roundtrip_any_nonempty_active
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ steps : Nat,
      ConfigRightBlankEq
        (parserMachine.run steps
          (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
            (none :: tail.reverse.map some ++
              List.replicate pad (none : Option Bool))
            log none))
        (phaseConfig 4 pad tail log') := by
  rcases nonempty_eq_reverse_append_last tail htail with
    ⟨rest, last, hshape⟩
  subst tail
  rcases leaf_afterEnd_roundtrip_nonempty_active
      pad hpad last rest log log' hpop hactive with
    ⟨steps, hsim⟩
  refine ⟨steps, ?_⟩
  simpa [List.map_append, List.append_assoc] using hsim


/-- Semantic simulation predicate for one abstract parser phase.  Runtime
bounding is intentionally separated from semantic correctness so the global
induction cannot hide a complexity assumption. -/
def PhaseSemantics
    (fuel : Nat)
    (pad : Nat)
    (log : SlotLog)
    (bits : BitString) : Prop :=
  ∃ steps : Nat,
    parserMachine.halting
        (parserMachine.run steps
          (phaseConfig 4 pad bits log)).state = true ∧
    (parserAccepting
        (parserMachine.run steps
          (phaseConfig 4 pad bits log)).state = true ↔
      CanonicalSATParserGlobalSpec.logParseCore fuel log bits = true)

/-- Compose an exact concrete phase prefix with a recursively certified phase.
-/
theorem phaseSemantics_compose_exact
    (parentFuel childFuel : Nat)
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        phaseConfig 4 childPad childBits childLog)
    (habstract :
      CanonicalSATParserGlobalSpec.logParseCore
          parentFuel parentLog parentBits =
        CanonicalSATParserGlobalSpec.logParseCore
          childFuel childLog childBits)
    (hchild :
      PhaseSemantics childFuel childPad childLog childBits) :
    PhaseSemantics parentFuel parentPad parentLog parentBits := by
  rcases hchild with ⟨steps, hhalt, hcorrect⟩
  refine ⟨prefixSteps + steps, ?_, ?_⟩
  · rw [MachineRunLemmas.run_add, hprefix]
    exact hhalt
  · rw [MachineRunLemmas.run_add, hprefix, habstract]
    exact hcorrect

/-- Same composition when the concrete prefixSteps reaches a tape-equivalent phase
modulo finitely many explicit far-right blanks.  State equality is enough for
halting and acceptance, while the parser-step bisimulation carries it through
the recursive suffix. -/
theorem phaseSemantics_compose_rightBlank
    (parentFuel childFuel : Nat)
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hprefix :
      ConfigRightBlankEq
        (parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog))
        (phaseConfig 4 childPad childBits childLog))
    (habstract :
      CanonicalSATParserGlobalSpec.logParseCore
          parentFuel parentLog parentBits =
        CanonicalSATParserGlobalSpec.logParseCore
          childFuel childLog childBits)
    (hchild :
      PhaseSemantics childFuel childPad childLog childBits) :
    PhaseSemantics parentFuel parentPad parentLog parentBits := by
  rcases hchild with ⟨steps, hhalt, hcorrect⟩
  have hrun :=
    parser_run_respects_right_blank steps hprefix
  have hstate :
      (parserMachine.run steps
        (parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog))).state =
      (parserMachine.run steps
        (phaseConfig 4 childPad childBits childLog)).state :=
    hrun.1
  refine ⟨prefixSteps + steps, ?_, ?_⟩
  · rw [MachineRunLemmas.run_add]
    rw [hstate]
    exact hhalt
  · rw [MachineRunLemmas.run_add]
    rw [hstate, habstract]
    exact hcorrect

theorem logParseCore_zero_slots
    (fuel : Nat)
    (hfuel : 0 < fuel)
    (log : SlotLog)
    (bits : BitString)
    (hzero : activeSlots log = 0) :
    CanonicalSATParserGlobalSpec.logParseCore fuel log bits =
      bits.isEmpty := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      simp [CanonicalSATParserGlobalSpec.logParseCore, hzero]

theorem logParseCore_active_empty
    (fuel : Nat)
    (hfuel : 0 < fuel)
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0) :
    CanonicalSATParserGlobalSpec.logParseCore fuel log [] = false := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      simp [CanonicalSATParserGlobalSpec.logParseCore, hactive, parseHead]


theorem phaseSemantics_of_reject_state
    (fuel pad : Nat)
    (log : SlotLog)
    (bits : BitString)
    (steps : Nat)
    (hstate :
      (parserMachine.run steps
        (phaseConfig 4 pad bits log)).state = (24 : Fin 25))
    (habstract :
      CanonicalSATParserGlobalSpec.logParseCore fuel log bits = false) :
    PhaseSemantics fuel pad log bits := by
  refine ⟨steps, ?_, ?_⟩
  · rw [hstate]
    decide
  · rw [hstate, habstract]
    decide

theorem phaseSemantics_of_accept_state
    (fuel pad : Nat)
    (log : SlotLog)
    (bits : BitString)
    (steps : Nat)
    (hstate :
      (parserMachine.run steps
        (phaseConfig 4 pad bits log)).state = (23 : Fin 25))
    (habstract :
      CanonicalSATParserGlobalSpec.logParseCore fuel log bits = true) :
    PhaseSemantics fuel pad log bits := by
  refine ⟨steps, ?_, ?_⟩
  · rw [hstate]
    decide
  · rw [hstate, habstract]
    decide

/-- Malformed-head semantics are now closed at the phase level. -/
theorem phaseSemantics_parseHead_none
    (fuel pad : Nat)
    (log : SlotLog)
    (bits : BitString)
    (hactive : activeSlots log ≠ 0)
    (hnone : parseHead bits = none) :
    PhaseSemantics (fuel + 1) pad log bits := by
  rcases phase_parseHead_none_state_rejects pad bits log hnone with
    ⟨steps, hstate⟩
  apply phaseSemantics_of_reject_state
    (fuel + 1) pad log bits steps hstate
  simp [CanonicalSATParserGlobalSpec.logParseCore, hactive, hnone]



/-- One successful INPUT head step, normalized to the canonical residual fuel. -/
theorem logParseCore_input_step_stable
    (bits rest : BitString)
    (log log' : SlotLog)
    (i : Nat)
    (hactive : activeSlots log ≠ 0)
    (hparse : parseHead bits = some (.input i, rest))
    (hpop : popSlot log = some log') :
    CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits =
      CanonicalSATParserGlobalSpec.logParseCore
        (rest.length + 1) log' rest := by
  have hlt : rest.length < bits.length :=
    parseHead_rest_length_lt hparse
  have hstep :
      CanonicalSATParserGlobalSpec.logParseCore
          (bits.length + 1) log bits =
        CanonicalSATParserGlobalSpec.logParseCore
          bits.length log' rest := by
    simp [CanonicalSATParserGlobalSpec.logParseCore,
      hactive, hparse, hpop]
  exact hstep.trans
    (logParseCore_fuel_stable rest log'
      bits.length (rest.length + 1) (by omega) (by omega))

/-- One successful CONST head step, normalized to the canonical residual fuel. -/
theorem logParseCore_const_step_stable
    (bits rest : BitString)
    (log log' : SlotLog)
    (b : Bool)
    (hactive : activeSlots log ≠ 0)
    (hparse : parseHead bits = some (.const b, rest))
    (hpop : popSlot log = some log') :
    CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits =
      CanonicalSATParserGlobalSpec.logParseCore
        (rest.length + 1) log' rest := by
  have hlt : rest.length < bits.length :=
    parseHead_rest_length_lt hparse
  have hstep :
      CanonicalSATParserGlobalSpec.logParseCore
          (bits.length + 1) log bits =
        CanonicalSATParserGlobalSpec.logParseCore
          bits.length log' rest := by
    simp [CanonicalSATParserGlobalSpec.logParseCore,
      hactive, hparse, hpop]
  exact hstep.trans
    (logParseCore_fuel_stable rest log'
      bits.length (rest.length + 1) (by omega) (by omega))

/-- One successful NOT head step, normalized to the canonical residual fuel. -/
theorem logParseCore_not_step_stable
    (bits rest : BitString)
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0)
    (hparse : parseHead bits = some (.not, rest)) :
    CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits =
      CanonicalSATParserGlobalSpec.logParseCore
        (rest.length + 1) log rest := by
  have hlt : rest.length < bits.length :=
    parseHead_rest_length_lt hparse
  have hstep :
      CanonicalSATParserGlobalSpec.logParseCore
          (bits.length + 1) log bits =
        CanonicalSATParserGlobalSpec.logParseCore
          bits.length log rest := by
    simp [CanonicalSATParserGlobalSpec.logParseCore,
      hactive, hparse]
  exact hstep.trans
    (logParseCore_fuel_stable rest log
      bits.length (rest.length + 1) (by omega) (by omega))

/-- One successful AND head step, normalized to the canonical residual fuel. -/
theorem logParseCore_and_step_stable
    (bits rest : BitString)
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0)
    (hparse : parseHead bits = some (.and, rest)) :
    CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits =
      CanonicalSATParserGlobalSpec.logParseCore
        (rest.length + 1) (pushSlot log) rest := by
  have hlt : rest.length < bits.length :=
    parseHead_rest_length_lt hparse
  have hstep :
      CanonicalSATParserGlobalSpec.logParseCore
          (bits.length + 1) log bits =
        CanonicalSATParserGlobalSpec.logParseCore
          bits.length (pushSlot log) rest := by
    simp [CanonicalSATParserGlobalSpec.logParseCore,
      hactive, hparse]
  exact hstep.trans
    (logParseCore_fuel_stable rest (pushSlot log)
      bits.length (rest.length + 1) (by omega) (by omega))

/-- One successful OR head step, normalized to the canonical residual fuel. -/
theorem logParseCore_or_step_stable
    (bits rest : BitString)
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0)
    (hparse : parseHead bits = some (.or, rest)) :
    CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits =
      CanonicalSATParserGlobalSpec.logParseCore
        (rest.length + 1) (pushSlot log) rest := by
  have hlt : rest.length < bits.length :=
    parseHead_rest_length_lt hparse
  have hstep :
      CanonicalSATParserGlobalSpec.logParseCore
          (bits.length + 1) log bits =
        CanonicalSATParserGlobalSpec.logParseCore
          bits.length (pushSlot log) rest := by
    simp [CanonicalSATParserGlobalSpec.logParseCore,
      hactive, hparse]
  exact hstep.trans
    (logParseCore_fuel_stable rest (pushSlot log)
      bits.length (rest.length + 1) (by omega) (by omega))



/-- Generic semantic closure for a leaf after the already-certified head/work
prefix has reached the physical pop-search configuration.  This packages all
four leaf continuations without duplicating INPUT/CONST reasoning. -/
theorem phaseSemantics_leaf_from_pop
    (parentFuel parentPad leafPad prefixSteps : Nat)
    (parentLog log' : SlotLog)
    (parentBits rest : BitString)
    (hpad : 0 < leafPad)
    (hpop : popSlot parentLog = some log')
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: rest.reverse.map some ++
            List.replicate leafPad (none : Option Bool))
          parentLog none)
    (habstract :
      CanonicalSATParserGlobalSpec.logParseCore
          parentFuel parentLog parentBits =
        CanonicalSATParserGlobalSpec.logParseCore
          (rest.length + 1) log' rest)
    (hchild :
      activeSlots log' ≠ 0 →
      rest ≠ [] →
      PhaseSemantics (rest.length + 1) leafPad log' rest) :
    PhaseSemantics parentFuel parentPad parentLog parentBits := by
  by_cases hzero : activeSlots log' = 0
  · by_cases hrest : rest = []
    · subst rest
      rcases
          leaf_afterEnd_inactive_exhausted_accepts
            leafPad hpad parentLog log' hpop hzero with
        ⟨leafSteps, right, hleaf⟩
      have hrun :
          parserMachine.run (prefixSteps + leafSteps)
              (phaseConfig 4 parentPad parentBits parentLog) =
            CanonicalSATParserLeafSourceProof.leafAcceptConfig
              leafPad right := by
        rw [MachineRunLemmas.run_add, hprefix]
        exact hleaf
      have hstate :
          (parserMachine.run (prefixSteps + leafSteps)
            (phaseConfig 4 parentPad parentBits parentLog)).state =
            (23 : Fin 25) := by
        rw [hrun]
        rfl
      have hchildTrue :
          CanonicalSATParserGlobalSpec.logParseCore 1 log' [] = true := by
        simp [CanonicalSATParserGlobalSpec.logParseCore, hzero]
      have habstractTrue :
          CanonicalSATParserGlobalSpec.logParseCore
              parentFuel parentLog parentBits = true := by
        exact habstract.trans hchildTrue
      exact
        phaseSemantics_of_accept_state
          parentFuel parentPad parentLog parentBits
          (prefixSteps + leafSteps) hstate habstractTrue
    · rcases
          leaf_afterEnd_inactive_residual_rejects
            leafPad hpad rest hrest parentLog log' hpop hzero with
        ⟨leafSteps, cfg, hleaf, hhalt, hreject⟩
      have hchildFalse :
          CanonicalSATParserGlobalSpec.logParseCore
              (rest.length + 1) log' rest = false := by
        rw [logParseCore_zero_slots
          (rest.length + 1) (by omega) log' rest hzero]
        cases rest with
        | nil => contradiction
        | cons b bs => rfl
      have habstractFalse :
          CanonicalSATParserGlobalSpec.logParseCore
              parentFuel parentLog parentBits = false := by
        exact habstract.trans hchildFalse
      refine ⟨prefixSteps + leafSteps, ?_, ?_⟩
      · rw [MachineRunLemmas.run_add, hprefix, hleaf]
        exact hhalt
      · rw [MachineRunLemmas.run_add, hprefix, hleaf, habstractFalse]
        simp [hreject]
  · have hactive : activeSlots log' ≠ 0 := hzero
    by_cases hrest : rest = []
    · subst rest
      rcases
          leaf_afterEnd_active_exhausted_rejects
            leafPad hpad parentLog log' hpop hactive with
        ⟨leafSteps, right, hleaf⟩
      have hrun :
          parserMachine.run (prefixSteps + leafSteps)
              (phaseConfig 4 parentPad parentBits parentLog) =
            CanonicalSATParserLeafSourceProof.leafRejectConfig
              leafPad right := by
        rw [MachineRunLemmas.run_add, hprefix]
        exact hleaf
      have hstate :
          (parserMachine.run (prefixSteps + leafSteps)
            (phaseConfig 4 parentPad parentBits parentLog)).state =
            (24 : Fin 25) := by
        rw [hrun]
        rfl
      have hchildFalse :
          CanonicalSATParserGlobalSpec.logParseCore 1 log' [] = false := by
        exact logParseCore_active_empty 1 (by omega) log' hactive
      have habstractFalse :
          CanonicalSATParserGlobalSpec.logParseCore
              parentFuel parentLog parentBits = false := by
        exact habstract.trans hchildFalse
      exact
        phaseSemantics_of_reject_state
          parentFuel parentPad parentLog parentBits
          (prefixSteps + leafSteps) hstate habstractFalse
    · rcases
          leaf_afterEnd_roundtrip_any_nonempty_active
            leafPad hpad rest hrest parentLog log' hpop hactive with
        ⟨leafSteps, hleaf⟩
      have hcombined :
          ConfigRightBlankEq
            (parserMachine.run (prefixSteps + leafSteps)
              (phaseConfig 4 parentPad parentBits parentLog))
            (phaseConfig 4 leafPad rest log') := by
        rw [MachineRunLemmas.run_add, hprefix]
        exact hleaf
      exact
        phaseSemantics_compose_rightBlank
          parentFuel (rest.length + 1)
          parentPad leafPad
          parentLog log'
          parentBits rest
          (prefixSteps + leafSteps)
          hcombined habstract
          (hchild hactive hrest)



/-- Global semantic simulation for every active parser phase, strengthened
to all unread sources of length at most n.  This permits ordinary Nat
induction while every successful canonical head strictly shortens the source.
No runtime bound is used here. -/
theorem phaseSemantics_active_up_to
    (n : Nat) :
    ∀ (bits : BitString) (log : SlotLog) (pad : Nat),
      bits.length ≤ n →
      activeSlots log ≠ 0 →
      0 < pad →
      PhaseSemantics (bits.length + 1) pad log bits := by
  induction n with
  | zero =>
      intro bits log pad hlen hactive hpad
      have hlen0 : bits.length = 0 := Nat.eq_zero_of_le_zero hlen
      have hbits : bits = [] := List.length_eq_zero.mp hlen0
      subst bits
      exact
        phaseSemantics_parseHead_none
          0 pad log [] hactive (by rfl)
  | succ n ih =>
      intro bits log pad hlen hactive hpad
      cases hparse : parseHead bits with
      | none =>
          exact
            phaseSemantics_parseHead_none
              bits.length pad log bits hactive hparse
      | some parsed =>
          rcases parsed with ⟨head, rest⟩
          have hlt : rest.length < bits.length :=
            parseHead_rest_length_lt hparse
          have hrestle : rest.length ≤ n := by
            omega
          have hshape : bits = head.encode ++ rest :=
            parseHead_inverse bits head rest hparse
          cases head with
          | input i =>
              rcases popSlot_exists_of_active log hactive with
                ⟨log', hpop⟩
              have habstract :=
                logParseCore_input_step_stable
                  bits rest log log' i hactive hparse hpop
              have hprefix :
                  parserMachine.run
                      (CanonicalSATParserPhaseMacroProof.headWorkFuel
                        (.input i) rest.length log.length)
                      (phaseConfig 4 pad bits log) =
                    CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
                      (none :: rest.reverse.map some ++
                        List.replicate
                          (pad + (Head.encode (.input i)).length)
                          (none : Option Bool))
                      log none := by
                rw [hshape]
                exact
                  CanonicalSATParserPhaseMacroProof.input_head_to_pop_search
                    pad i rest log
              refine
                phaseSemantics_leaf_from_pop
                  (parentFuel := bits.length + 1)
                  (parentPad := pad)
                  (leafPad := pad + (Head.encode (.input i)).length)
                  (prefixSteps :=
                    CanonicalSATParserPhaseMacroProof.headWorkFuel
                      (.input i) rest.length log.length)
                  (parentLog := log)
                  (log' := log')
                  (parentBits := bits)
                  (rest := rest)
                  (by omega) hpop hprefix habstract ?_
              intro hactive' hrest
              exact
                ih rest log'
                  (pad + (Head.encode (.input i)).length)
                  hrestle hactive' (by omega)
          | const b =>
              rcases popSlot_exists_of_active log hactive with
                ⟨log', hpop⟩
              have habstract :=
                logParseCore_const_step_stable
                  bits rest log log' b hactive hparse hpop
              have hprefix :
                  parserMachine.run
                      (CanonicalSATParserPhaseMacroProof.headWorkFuel
                        (.const b) rest.length log.length)
                      (phaseConfig 4 pad bits log) =
                    CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
                      (none :: rest.reverse.map some ++
                        List.replicate
                          (pad + (Head.encode (.const b)).length)
                          (none : Option Bool))
                      log none := by
                rw [hshape]
                exact
                  CanonicalSATParserPhaseMacroProof.const_head_to_pop_search
                    pad b rest log
              refine
                phaseSemantics_leaf_from_pop
                  (parentFuel := bits.length + 1)
                  (parentPad := pad)
                  (leafPad := pad + (Head.encode (.const b)).length)
                  (prefixSteps :=
                    CanonicalSATParserPhaseMacroProof.headWorkFuel
                      (.const b) rest.length log.length)
                  (parentLog := log)
                  (log' := log')
                  (parentBits := bits)
                  (rest := rest)
                  (by omega) hpop hprefix habstract ?_
              intro hactive' hrest
              exact
                ih rest log'
                  (pad + (Head.encode (.const b)).length)
                  hrestle hactive' (by omega)
          | not =>
              have habstract :=
                logParseCore_not_step_stable
                  bits rest log hactive hparse
              have hprefix :
                  parserMachine.run (Head.encode .not).length
                      (phaseConfig 4 pad bits log) =
                    phaseConfig 4
                      (pad + (Head.encode .not).length) rest log := by
                rw [hshape]
                exact
                  CanonicalSATParserPhaseMacroProof.not_head_roundtrip
                    pad rest log
              have hchild :
                  PhaseSemantics (rest.length + 1)
                    (pad + (Head.encode .not).length) log rest :=
                ih rest log
                  (pad + (Head.encode .not).length)
                  hrestle hactive (by omega)
              exact
                phaseSemantics_compose_exact
                  (bits.length + 1) (rest.length + 1)
                  pad (pad + (Head.encode .not).length)
                  log log bits rest
                  (Head.encode .not).length
                  hprefix habstract hchild
          | and =>
              have habstract :=
                logParseCore_and_step_stable
                  bits rest log hactive hparse
              by_cases hrest : rest = []
              · subst rest
                have hrun :
                    parserMachine.run
                        (CanonicalSATParserPhaseMacroProof.headWorkFuel
                            Head.and 0 log.length +
                          (log.length + 2))
                        (phaseConfig 4 pad bits log) =
                      CanonicalSATParserLeafSourceProof.leafRejectConfig
                        (pad + (Head.encode .and).length)
                        ((pushSlot log).map some) := by
                  rw [hshape]
                  simpa using
                    CanonicalSATParserBinaryHeadProof.and_head_exhausted_rejects
                      pad hpad log
                have hstate :
                    (parserMachine.run
                        (CanonicalSATParserPhaseMacroProof.headWorkFuel
                            Head.and 0 log.length +
                          (log.length + 2))
                        (phaseConfig 4 pad bits log)).state =
                      (24 : Fin 25) := by
                  rw [hrun]
                  rfl
                have hpush : activeSlots (pushSlot log) ≠ 0 := by
                  rw [activeSlots_pushSlot]
                  omega
                have hchildFalse :
                    CanonicalSATParserGlobalSpec.logParseCore
                        1 (pushSlot log) [] = false :=
                  logParseCore_active_empty 1 (by omega)
                    (pushSlot log) hpush
                have habstractFalse :
                    CanonicalSATParserGlobalSpec.logParseCore
                        (bits.length + 1) log bits = false := by
                  exact habstract.trans hchildFalse
                exact
                  phaseSemantics_of_reject_state
                    (bits.length + 1) pad log bits
                    (CanonicalSATParserPhaseMacroProof.headWorkFuel
                        Head.and 0 log.length +
                      (log.length + 2))
                    hstate habstractFalse
              · have hpush : activeSlots (pushSlot log) ≠ 0 := by
                  rw [activeSlots_pushSlot]
                  omega
                rcases
                    and_head_roundtrip_any_nonempty
                      pad hpad rest hrest log with
                  ⟨prefixSteps, hprefix⟩
                have hchild :
                    PhaseSemantics (rest.length + 1)
                      (pad + (Head.encode .and).length)
                      (pushSlot log) rest :=
                  ih rest (pushSlot log)
                    (pad + (Head.encode .and).length)
                    hrestle hpush (by omega)
                exact
                  phaseSemantics_compose_exact
                    (bits.length + 1) (rest.length + 1)
                    pad (pad + (Head.encode .and).length)
                    log (pushSlot log)
                    bits rest
                    prefixSteps
                    (by
                      rw [hshape]
                      exact hprefix)
                    habstract hchild
          | or =>
              have habstract :=
                logParseCore_or_step_stable
                  bits rest log hactive hparse
              by_cases hrest : rest = []
              · subst rest
                have hrun :
                    parserMachine.run
                        (CanonicalSATParserPhaseMacroProof.headWorkFuel
                            Head.or 0 log.length +
                          (log.length + 2))
                        (phaseConfig 4 pad bits log) =
                      CanonicalSATParserLeafSourceProof.leafRejectConfig
                        (pad + (Head.encode .or).length)
                        ((pushSlot log).map some) := by
                  rw [hshape]
                  simpa using
                    CanonicalSATParserBinaryHeadProof.or_head_exhausted_rejects
                      pad hpad log
                have hstate :
                    (parserMachine.run
                        (CanonicalSATParserPhaseMacroProof.headWorkFuel
                            Head.or 0 log.length +
                          (log.length + 2))
                        (phaseConfig 4 pad bits log)).state =
                      (24 : Fin 25) := by
                  rw [hrun]
                  rfl
                have hpush : activeSlots (pushSlot log) ≠ 0 := by
                  rw [activeSlots_pushSlot]
                  omega
                have hchildFalse :
                    CanonicalSATParserGlobalSpec.logParseCore
                        1 (pushSlot log) [] = false :=
                  logParseCore_active_empty 1 (by omega)
                    (pushSlot log) hpush
                have habstractFalse :
                    CanonicalSATParserGlobalSpec.logParseCore
                        (bits.length + 1) log bits = false := by
                  exact habstract.trans hchildFalse
                exact
                  phaseSemantics_of_reject_state
                    (bits.length + 1) pad log bits
                    (CanonicalSATParserPhaseMacroProof.headWorkFuel
                        Head.or 0 log.length +
                      (log.length + 2))
                    hstate habstractFalse
              · have hpush : activeSlots (pushSlot log) ≠ 0 := by
                  rw [activeSlots_pushSlot]
                  omega
                rcases
                    or_head_roundtrip_any_nonempty
                      pad hpad rest hrest log with
                  ⟨prefixSteps, hprefix⟩
                have hchild :
                    PhaseSemantics (rest.length + 1)
                      (pad + (Head.encode .or).length)
                      (pushSlot log) rest :=
                  ih rest (pushSlot log)
                    (pad + (Head.encode .or).length)
                    hrestle hpush (by omega)
                exact
                  phaseSemantics_compose_exact
                    (bits.length + 1) (rest.length + 1)
                    pad (pad + (Head.encode .or).length)
                    log (pushSlot log)
                    bits rest
                    prefixSteps
                    (by
                      rw [hshape]
                      exact hprefix)
                    habstract hchild

/-- The active-phase theorem specialized to the exact source length. -/
theorem phaseSemantics_active
    (bits : BitString)
    (log : SlotLog)
    (pad : Nat)
    (hactive : activeSlots log ≠ 0)
    (hpad : 0 < pad) :
    PhaseSemantics (bits.length + 1) pad log bits :=
  phaseSemantics_active_up_to bits.length
    bits log pad (by omega) hactive hpad

#print axioms MCore.Real.P01GlobalParserSimulation.phaseSemantics_of_reject_state
#print axioms MCore.Real.P01GlobalParserSimulation.phaseSemantics_of_accept_state
#print axioms MCore.Real.P01GlobalParserSimulation.phaseSemantics_parseHead_none

#print axioms MCore.Real.P01GlobalParserSimulation.phaseSemantics_compose_exact
#print axioms MCore.Real.P01GlobalParserSimulation.phaseSemantics_compose_rightBlank
#print axioms MCore.Real.P01GlobalParserSimulation.logParseCore_zero_slots
#print axioms MCore.Real.P01GlobalParserSimulation.logParseCore_active_empty

#print axioms MCore.Real.P01GlobalParserSimulation.and_head_roundtrip_any_nonempty
#print axioms MCore.Real.P01GlobalParserSimulation.or_head_roundtrip_any_nonempty
#print axioms MCore.Real.P01GlobalParserSimulation.leaf_afterEnd_roundtrip_any_nonempty_active

#print axioms MCore.Real.P01GlobalParserSimulation.decodeNat_none_eq_replicate_true
#print axioms MCore.Real.P01GlobalParserSimulation.q10_true_payload_rejects
#print axioms MCore.Real.P01GlobalParserSimulation.phase_parseHead_none_rejects

#print axioms MCore.Real.P01GlobalParserSimulation.nonempty_eq_reverse_append_last
#print axioms MCore.Real.P01GlobalParserSimulation.leaf_afterEnd_inactive_exhausted_accepts
#print axioms MCore.Real.P01GlobalParserSimulation.leaf_afterEnd_inactive_residual_rejects
#print axioms MCore.Real.P01GlobalParserSimulation.leaf_afterEnd_active_exhausted_rejects

#print axioms MCore.Real.P01GlobalParserSimulation.parser_step_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parser_run_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parseHead_rest_length_lt
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_length
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_exists_of_active

end P01GlobalParserSimulation
end Real
end MCore
