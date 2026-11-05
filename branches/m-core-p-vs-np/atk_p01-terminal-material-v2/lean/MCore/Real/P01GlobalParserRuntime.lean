import MCore.Real.P01GlobalParserSimulation

namespace MCore
namespace Real
namespace P01GlobalParserRuntime

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserLeafPopProof
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserWorkScanProof
open CanonicalSATSlotLog
open CanonicalSATSlotParserSpec
open MachineRunLemmas
open P01GlobalParserSimulation

private theorem map_some_false_suffix
    (suffix : SlotLog)
    (hall : ∀ b ∈ suffix, b = false) :
    suffix.map some =
      List.replicate suffix.length (some false) := by
  have hs :=
    CanonicalSATParserLeafPopProof.all_false_eq_replicate suffix hall
  rw [hs]
  simp

/-- Exact step count for the physical leaf-pop path when an older active slot
remains.  The source-check state is reached in exactly log.length+1 steps. -/
theorem leaf_afterEnd_active_to_source_exact
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    parserMachine.run (log.length + 1)
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
    simpa [P01GlobalParserSimulation.activeSlots_reverse] using hpre
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  have hlen :
      log.length + 1 =
        (suffix.length + 1) + (pre.length + 1) := by
    rw [hlog]
    simp [List.length_append]
    omega
  rw [hlen, MachineRunLemmas.run_add, hlog]
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

/-- Exact step count for the physical leaf-pop path when no active slot
remains. -/
theorem leaf_afterEnd_inactive_to_source_exact
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    parserMachine.run (log.length + 1)
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
  have hlen :
      log.length + 1 =
        (suffix.length + 1) + (pre.length + 1) := by
    rw [hlog]
    simp [List.length_append]
    omega
  rw [hlen, MachineRunLemmas.run_add, hlog]
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

/-- Exact active-leaf return count through source rewind. -/
theorem leaf_afterEnd_roundtrip_nonempty_active_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ConfigRightBlankEq
      (parserMachine.run
        ((log.length + 1) + (rest.length + 2))
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: some last ::
            (rest.map some ++
              List.replicate pad (none : Option Bool)))
          log none))
      (phaseConfig 4 pad (rest.reverse ++ [last]) log') := by
  let sourceLeft : List (Option Bool) :=
    some last ::
      (rest.map some ++ List.replicate pad (none : Option Bool))
  rw [MachineRunLemmas.run_add]
  have hsource :=
    leaf_afterEnd_active_to_source_exact
      sourceLeft log log' hpop hactive
  rw [show
      parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: some last ::
            (rest.map some ++
              List.replicate pad (none : Option Bool)))
          log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some ++ [none]) by
      simpa [sourceLeft] using hsource]
  have hcfg :=
    P01GlobalParserSimulation.leafSourceCheck_trailing_blank
      (17 : Fin 25) sourceLeft (log'.map some)
  have hrun :=
    P01GlobalParserSimulation.parser_run_respects_right_blank
      (rest.length + 2) hcfg
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


/-- Exact terminal count when the last active slot is consumed exactly at end
of source. -/
theorem leaf_afterEnd_inactive_exhausted_accepts_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ right : List (Option Bool),
      parserMachine.run (log.length + 2)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafSourceProof.leafAcceptConfig pad right := by
  let right := log'.map some ++ [none]
  refine ⟨right, ?_⟩
  rw [show log.length + 2 = (log.length + 1) + 1 by omega]
  rw [MachineRunLemmas.run_add]
  rw [leaf_afterEnd_inactive_to_source_exact
    (List.replicate pad (none : Option Bool)) log log' hpop hzero]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf16_exhausted_accepts
      pad hpad right
  simpa [TM.run, right] using hstep

/-- Exact terminal count when the last active slot is consumed while residual
source remains. -/
theorem leaf_afterEnd_inactive_residual_rejects_exact
    (pad : Nat)
    (tail : BitString)
    (htail : tail ≠ [])
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ cfg : Configuration (Fin 25) (Option Bool),
      parserMachine.run (log.length + 2)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: tail.reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none) = cfg ∧
      parserMachine.halting cfg.state = true ∧
      parserAccepting cfg.state = false := by
  rcases P01GlobalParserSimulation.nonempty_eq_reverse_append_last tail htail with
    ⟨rest, last, htailShape⟩
  subst tail
  let sourceLeft : List (Option Bool) :=
    some last :: (rest.map some ++ List.replicate pad (none : Option Bool))
  let right := log'.map some ++ [none]
  let cfg :=
    CanonicalSATParserTerminalBranches.leafResidualRejectConfig
      pad last rest right
  refine ⟨cfg, ?_, ?_, ?_⟩
  · rw [show log.length + 2 = (log.length + 1) + 1 by omega]
    rw [MachineRunLemmas.run_add]
    have hsource :=
      leaf_afterEnd_inactive_to_source_exact
        sourceLeft log log' hpop hzero
    rw [show
      parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: (rest.reverse ++ [last]).reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          16 sourceLeft (log'.map some ++ [none]) by
      simpa [sourceLeft, List.map_append, List.append_assoc] using hsource]
    have hstep :=
      CanonicalSATParserTerminalBranches.leaf16_residual_rejects
        pad last rest right
    simpa [TM.run, cfg, right, sourceLeft] using hstep
  · exact
      CanonicalSATParserTerminalBranches.leafResidualRejectConfig_halted
        pad last rest right
  · simp [cfg, CanonicalSATParserTerminalBranches.leafResidualRejectConfig,
      parserAccepting]

/-- Exact terminal count when source is exhausted but an older active slot
remains after the leaf pop. -/
theorem leaf_afterEnd_active_exhausted_rejects_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ right : List (Option Bool),
      parserMachine.run (log.length + 2)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafSourceProof.leafRejectConfig pad right := by
  let right := log'.map some ++ [none]
  refine ⟨right, ?_⟩
  rw [show log.length + 2 = (log.length + 1) + 1 by omega]
  rw [MachineRunLemmas.run_add]
  rw [leaf_afterEnd_active_to_source_exact
    (List.replicate pad (none : Option Bool)) log log' hpop hactive]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf17_exhausted_rejects
      pad hpad right
  simpa [TM.run, right] using hstep


/-- Reparameterized exact active-leaf return for an arbitrary nonempty unread
suffix. -/
theorem leaf_afterEnd_roundtrip_any_nonempty_active_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ConfigRightBlankEq
      (parserMachine.run
        ((log.length + 1) + (tail.length + 1))
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: tail.reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none))
      (phaseConfig 4 pad tail log') := by
  rcases P01GlobalParserSimulation.nonempty_eq_reverse_append_last
      tail htail with ⟨rest, last, hshape⟩
  subst tail
  have h :=
    leaf_afterEnd_roundtrip_nonempty_active_exact
      pad hpad last rest log log' hpop hactive
  simpa [List.map_append, List.append_assoc] using h

/-- Exact binary-head roundtrip count on every nonempty unread suffix. -/
theorem and_head_roundtrip_any_nonempty_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log : SlotLog) :
    parserMachine.run
        (CanonicalSATParserPhaseMacroProof.headWorkFuel
            Head.and tail.length log.length +
          (log.length + tail.length + 2))
        (phaseConfig 4 pad (Head.encode .and ++ tail) log) =
      phaseConfig 4
        (pad + (Head.encode .and).length)
        tail (pushSlot log) := by
  rcases P01GlobalParserSimulation.nonempty_eq_reverse_append_last
      tail htail with ⟨rest, last, hshape⟩
  subst tail
  have h :=
    CanonicalSATParserBinaryHeadProof.and_head_roundtrip_nonempty
      pad hpad last rest log
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem or_head_roundtrip_any_nonempty_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log : SlotLog) :
    parserMachine.run
        (CanonicalSATParserPhaseMacroProof.headWorkFuel
            Head.or tail.length log.length +
          (log.length + tail.length + 2))
        (phaseConfig 4 pad (Head.encode .or ++ tail) log) =
      phaseConfig 4
        (pad + (Head.encode .or).length)
        tail (pushSlot log) := by
  rcases P01GlobalParserSimulation.nonempty_eq_reverse_append_last
      tail htail with ⟨rest, last, hshape⟩
  subst tail
  have h :=
    CanonicalSATParserBinaryHeadProof.or_head_roundtrip_nonempty
      pad hpad last rest log
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Final-slot leaf with exhausted source reaches the canonical accept state in
exactly log.length+2 post-head steps. -/
theorem leaf_afterEnd_inactive_exhausted_accept_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    parserMachine.run (log.length + 2)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
      CanonicalSATParserLeafSourceProof.leafAcceptConfig
        pad (log'.map some ++ [none]) := by
  rw [show log.length + 2 = (log.length + 1) + 1 by omega]
  rw [MachineRunLemmas.run_add]
  rw [leaf_afterEnd_inactive_to_source_exact
    (List.replicate pad (none : Option Bool)) log log' hpop hzero]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf16_exhausted_accepts
      pad hpad (log'.map some ++ [none])
  simpa [TM.run] using hstep

/-- Exhausted source with an older active slot reaches the canonical reject
state in exactly log.length+2 post-head steps. -/
theorem leaf_afterEnd_active_exhausted_reject_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    parserMachine.run (log.length + 2)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: List.replicate pad (none : Option Bool))
          log none) =
      CanonicalSATParserLeafSourceProof.leafRejectConfig
        pad (log'.map some ++ [none]) := by
  rw [show log.length + 2 = (log.length + 1) + 1 by omega]
  rw [MachineRunLemmas.run_add]
  rw [leaf_afterEnd_active_to_source_exact
    (List.replicate pad (none : Option Bool)) log log' hpop hactive]
  have hstep :=
    CanonicalSATParserLeafSourceProof.leaf17_exhausted_rejects
      pad hpad (log'.map some ++ [none])
  simpa [TM.run] using hstep

/-- If source remains after the final active slot is consumed, the parser is
halted/rejecting after exactly log.length+2 post-head steps. -/
theorem leaf_afterEnd_inactive_residual_halts_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (tail : BitString)
    (htail : tail ≠ [])
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    parserMachine.HaltsWithin (log.length + 2)
      (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
        (none :: tail.reverse.map some ++
          List.replicate pad (none : Option Bool))
        log none) := by
  rcases P01GlobalParserSimulation.nonempty_eq_reverse_append_last
      tail htail with ⟨rest, last, hshape⟩
  subst tail
  have hrev :
      (rest.reverse ++ [last]).reverse.map some =
        some last :: rest.map some := by
    simp [List.map_append]
  unfold TM.HaltsWithin
  rw [show log.length + 2 = (log.length + 1) + 1 by omega]
  rw [MachineRunLemmas.run_add]
  have hsource :=
    leaf_afterEnd_inactive_to_source_exact
      (some last ::
        (rest.map some ++ List.replicate pad (none : Option Bool)))
      log log' hpop hzero
  rw [show
      parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: (rest.reverse ++ [last]).reverse.map some ++
            List.replicate pad (none : Option Bool))
          log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log'.map some ++ [none]) by
      simpa [hrev, List.append_assoc] using hsource]
  have hstep :=
    CanonicalSATParserTerminalBranches.leaf16_residual_rejects
      pad last rest (log'.map some ++ [none])
  rw [show
      parserMachine.run 1
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log'.map some ++ [none])) =
        CanonicalSATParserTerminalBranches.leafResidualRejectConfig
          pad last rest (log'.map some ++ [none]) by
      simpa [TM.run] using hstep]
  exact
    CanonicalSATParserTerminalBranches.leafResidualRejectConfig_halted
      pad last rest (log'.map some ++ [none])

/-- Malformed head rejection always happens within one more step than the
remaining source length. -/
theorem phase_parseHead_none_reject_bound
    (pad : Nat)
    (bits : BitString)
    (log : SlotLog)
    (hnone : CanonicalSATSlotParserSpec.parseHead bits = none) :
    ∃ steps : Nat,
      steps ≤ bits.length + 1 ∧
      (parserMachine.run steps
        (phaseConfig 4 pad bits log)).state = (24 : Fin 25) := by
  cases bits with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      simp [TM.run, phaseConfig, parserMachine, TM.step, Tape.write, Tape.move]
  | cons b1 r1 =>
      cases r1 with
      | nil =>
          cases b1
          · refine ⟨2, by simp, ?_⟩
            simp [TM.run, phaseConfig, parserMachine, TM.step,
              Tape.write, Tape.move]
          · refine ⟨2, by simp, ?_⟩
            simp [TM.run, phaseConfig, parserMachine, TM.step,
              Tape.write, Tape.move]
      | cons b2 r2 =>
          cases r2 with
          | nil =>
              cases b1 <;> cases b2
              · refine ⟨3, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨3, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨3, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨2, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
          | cons b3 rest =>
              cases b1 <;> cases b2 <;> cases b3
              · have hdec :
                    CanonicalCircuitBits.decodeNat rest = none := by
                  cases hd : CanonicalCircuitBits.decodeNat rest with
                  | none => rfl
                  | some p =>
                      rcases p with ⟨i, tail⟩
                      simp [CanonicalSATSlotParserSpec.parseHead, hd] at hnone
                have hrep :=
                  P01GlobalParserSimulation.decodeNat_none_eq_replicate_true
                    rest hdec
                rw [hrep]
                refine ⟨3 + (rest.length + 1), by simp; omega, ?_⟩
                rw [MachineRunLemmas.run_add]
                rw [CanonicalSATParserHeadProof.tag_input_run]
                rw [P01GlobalParserSimulation.q10_true_payload_rejects
                  (pad + 3) rest.length log]
                rfl
              · simp [CanonicalSATSlotParserSpec.parseHead] at hnone
              · simp [CanonicalSATSlotParserSpec.parseHead] at hnone
              · simp [CanonicalSATSlotParserSpec.parseHead] at hnone
              · simp [CanonicalSATSlotParserSpec.parseHead] at hnone
              · simp [CanonicalSATSlotParserSpec.parseHead] at hnone
              · refine ⟨2, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]
              · refine ⟨2, by simp, ?_⟩
                simp [TM.run, phaseConfig, parserMachine, TM.step,
                  Tape.write, Tape.move]

#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_active_to_source_exact
#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_inactive_to_source_exact
#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_roundtrip_nonempty_active_exact

end P01GlobalParserRuntime
end Real
end MCore
