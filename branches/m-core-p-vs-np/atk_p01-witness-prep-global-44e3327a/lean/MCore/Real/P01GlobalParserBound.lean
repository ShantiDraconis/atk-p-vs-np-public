import MCore.Real.P01GlobalParserRuntime

namespace MCore
namespace Real
namespace P01GlobalParserBound

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog
open MachineRunLemmas
open P01GlobalParserSimulation
open P01GlobalParserRuntime

/-- Local tape-footprint scale used only for the runtime proof. -/
def phaseRuntimeScale
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  pad + bits.length + log.length + 1

/-- One macro-step allowance at a fixed local footprint. -/
def phaseRuntimeUnit
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  16 * phaseRuntimeScale pad log bits

/-- Quadratic phase budget. Every successful head strictly shortens bits. -/
def phaseRuntimeBudget
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  phaseRuntimeUnit pad log bits * (bits.length + 1)

theorem phaseRuntimeScale_pos
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeScale pad log bits := by
  simp [phaseRuntimeScale]

theorem phaseRuntimeUnit_pos
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeUnit pad log bits := by
  unfold phaseRuntimeUnit
  exact Nat.mul_pos (by decide) (phaseRuntimeScale_pos pad hpad log bits)

/-- If the local footprint scale is unchanged, one unit pays for the concrete
prefix and the residual budget strictly decreases with unread-source length. -/
theorem budget_compose_same_scale
    (S parentLen childLen prefixSteps : Nat)
    (hlt : childLen < parentLen)
    (hprefix : prefixSteps ≤ 16 * S) :
    prefixSteps + (16 * S * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hlen : childLen + 2 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 2) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefixSteps + (16 * S * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 1)) :=
      Nat.add_le_add_right hprefix _
    _ = 16 * S * (childLen + 2) := by
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ 16 * S * (parentLen + 1) := hmul

/-- Binary heads add one tombstone-log cell but consume three source bits.
The extra scale cell is absorbed by the three-bit source decrease. -/
theorem budget_compose_scale_succ
    (S parentLen childLen prefixSteps : Nat)
    (hchildScale : childLen + 1 ≤ S)
    (hconsume : childLen + 3 ≤ parentLen)
    (hprefix : prefixSteps ≤ 16 * S) :
    prefixSteps + (16 * (S + 1) * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hscale :
      (S + 1) * (childLen + 1) ≤ S * (childLen + 2) := by
    calc
      (S + 1) * (childLen + 1)
          = S * (childLen + 1) + (childLen + 1) := by
        rw [show S + 1 = Nat.succ S by omega]
        rw [Nat.succ_mul]
      _ ≤ S * (childLen + 1) + S :=
        Nat.add_le_add_left hchildScale _
      _ = S * (childLen + 2) := by
        simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hscale16 :
      16 * ((S + 1) * (childLen + 1)) ≤
        16 * (S * (childLen + 2)) :=
    Nat.mul_le_mul_left 16 hscale
  have hchild :
      16 * (S + 1) * (childLen + 1) ≤
        16 * S * (childLen + 2) := by
    simpa [Nat.mul_assoc] using hscale16
  have hprechild :
      prefixSteps + (16 * (S + 1) * (childLen + 1)) ≤
        16 * S + (16 * S * (childLen + 2)) :=
    Nat.add_le_add hprefix hchild
  have hlen : childLen + 3 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 3) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefixSteps + (16 * (S + 1) * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 2)) := hprechild
    _ = 16 * S * (childLen + 3) := by
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ 16 * S * (parentLen + 1) := hmul

theorem phaseBudget_positive
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  exact Nat.mul_pos
    (phaseRuntimeUnit_pos pad hpad log bits)
    (by omega)


/-- One local runtime unit is always contained in the quadratic phase budget. -/
theorem phaseRuntimeUnit_le_budget
    (pad : Nat) (log : SlotLog) (bits : BitString) :
    phaseRuntimeUnit pad log bits ≤ phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  have h : 1 ≤ bits.length + 1 := by omega
  have hm :=
    Nat.mul_le_mul_left (phaseRuntimeUnit pad log bits) h
  simpa using hm

/-- Every exact head/work/return prefix used by a recursive parser phase fits
inside one local runtime unit. -/
theorem phasePrefixLinear_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (head : Head) (tail : BitString) (log : SlotLog) :
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        head tail.length log.length +
      (log.length + tail.length + 2) ≤
        phaseRuntimeUnit pad log (head.encode ++ tail) := by
  unfold phaseRuntimeUnit phaseRuntimeScale
  unfold CanonicalSATParserPhaseMacroProof.headWorkFuel
  unfold CanonicalSATParserMacroProof.phaseWorkBound
  simp only [List.length_append]
  omega

theorem phasePrefixTerminal_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (head : Head) (tail : BitString) (log : SlotLog) :
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        head tail.length log.length +
      (log.length + 2) ≤
        phaseRuntimeUnit pad log (head.encode ++ tail) := by
  have h := phasePrefixLinear_le_unit pad hpad head tail log
  omega

theorem phasePrefixNot_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (tail : BitString) (log : SlotLog) :
    (Head.encode .not).length ≤
      phaseRuntimeUnit pad log (Head.encode .not ++ tail) := by
  unfold phaseRuntimeUnit phaseRuntimeScale
  simp only [List.length_append]
  omega

theorem phaseRuntimeScale_same
    (pad : Nat) (head : Head)
    (tail : BitString) (log : SlotLog) :
    phaseRuntimeScale
        (pad + head.encode.length) log tail =
      phaseRuntimeScale pad log (head.encode ++ tail) := by
  unfold phaseRuntimeScale
  simp only [List.length_append]
  omega

theorem phaseRuntimeScale_pop_same
    (pad : Nat) (head : Head)
    (tail : BitString) (log log' : SlotLog)
    (hpop : popSlot log = some log') :
    phaseRuntimeScale
        (pad + head.encode.length) log' tail =
      phaseRuntimeScale pad log (head.encode ++ tail) := by
  have hlen := popSlot_length hpop
  unfold phaseRuntimeScale
  simp only [List.length_append]
  rw [hlen]
  omega

theorem phaseRuntimeScale_push_succ
    (pad : Nat) (head : Head)
    (tail : BitString) (log : SlotLog) :
    phaseRuntimeScale
        (pad + head.encode.length) (pushSlot log) tail =
      phaseRuntimeScale pad log (head.encode ++ tail) + 1 := by
  unfold phaseRuntimeScale
  simp [CanonicalSATSlotLog.pushSlot, List.length_append]
  omega

theorem parser_halts_after_exact_prefix
    (parent child : Configuration (Fin 25) (Option Bool))
    (prefixSteps childBudget : Nat)
    (hprefix :
      parserMachine.run prefixSteps parent = child)
    (hchild :
      parserMachine.HaltsWithin childBudget child) :
    parserMachine.HaltsWithin (prefixSteps + childBudget) parent := by
  unfold TM.HaltsWithin at hchild ⊢
  rw [MachineRunLemmas.run_add, hprefix]
  exact hchild

theorem parser_halts_after_rightBlank_prefix
    (parent child : Configuration (Fin 25) (Option Bool))
    (prefixSteps childBudget : Nat)
    (hprefix :
      ConfigRightBlankEq
        (parserMachine.run prefixSteps parent) child)
    (hchild :
      parserMachine.HaltsWithin childBudget child) :
    parserMachine.HaltsWithin (prefixSteps + childBudget) parent := by
  unfold TM.HaltsWithin at hchild ⊢
  rw [MachineRunLemmas.run_add]
  have hrun :=
    parser_run_respects_right_blank childBudget hprefix
  rw [hrun.1]
  exact hchild


theorem parser_terminal_halt_to_budget
    (pad : Nat) (log : SlotLog) (bits : BitString)
    (steps : Nat)
    (hsteps : steps ≤ phaseRuntimeUnit pad log bits)
    (hhalt :
      parserMachine.HaltsWithin steps (phaseConfig 4 pad bits log)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget pad log bits)
      (phaseConfig 4 pad bits log) := by
  have hle :=
    Nat.le_trans hsteps (phaseRuntimeUnit_le_budget pad log bits)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 pad bits log) hle hhalt

theorem parser_compose_same_scale_exact_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hlt : childBits.length < parentBits.length)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        phaseConfig 4 childPad childBits childLog)
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_exact_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_same_scale
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hlt (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall

theorem parser_compose_same_scale_rightBlank_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hlt : childBits.length < parentBits.length)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      ConfigRightBlankEq
        (parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog))
        (phaseConfig 4 childPad childBits childLog))
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_rightBlank_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_same_scale
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hlt (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall

theorem parser_compose_scale_succ_exact_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits + 1)
    (hchildScale :
      childBits.length + 1 ≤
        phaseRuntimeScale parentPad parentLog parentBits)
    (hconsume :
      childBits.length + 3 ≤ parentBits.length)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        phaseConfig 4 childPad childBits childLog)
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_exact_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_scale_succ
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hchildScale hconsume
      (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall


/-- Generic bounded leaf phase.  INPUT and CONST instantiate this with their
already-certified head-to-pop-search macro. -/
theorem leaf_head_halts_budget
    (pad : Nat) (log : SlotLog)
    (bits tail : BitString) (head : Head)
    (hpad : 0 < pad)
    (hactive : activeSlots log ≠ 0)
    (hlt : tail.length < bits.length)
    (hshape : bits = head.encode ++ tail)
    (hhead :
      parserMachine.run
          (CanonicalSATParserPhaseMacroProof.headWorkFuel
            head tail.length log.length)
          (phaseConfig 4 pad bits log) =
        CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: tail.reverse.map some ++
            List.replicate
              (pad + head.encode.length)
              (none : Option Bool))
          log none)
    (hchild :
      ∀ log' : SlotLog,
        popSlot log = some log' →
        activeSlots log' ≠ 0 →
        tail ≠ [] →
        parserMachine.HaltsWithin
          (phaseRuntimeBudget
            (pad + head.encode.length) log' tail)
          (phaseConfig 4
            (pad + head.encode.length) tail log')) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget pad log bits)
      (phaseConfig 4 pad bits log) := by
  rcases popSlot_exists_of_active log hactive with ⟨log', hpop⟩
  let hs :=
    CanonicalSATParserPhaseMacroProof.headWorkFuel
      head tail.length log.length
  by_cases hzero : activeSlots log' = 0
  · by_cases htail : tail = []
    · subst tail
      let steps := hs + (log.length + 2)
      rcases leaf_afterEnd_inactive_exhausted_accepts_exact
          (pad + head.encode.length) (by omega)
          log log' hpop hzero with ⟨right, hleaf⟩
      have hrun :
          parserMachine.run steps (phaseConfig 4 pad bits log) =
            CanonicalSATParserLeafSourceProof.leafAcceptConfig
              (pad + head.encode.length) right := by
        dsimp [steps, hs]
        rw [MachineRunLemmas.run_add]
        have hhead0 := hhead
        simp only [List.length_nil, List.reverse_nil, List.map_nil,
          List.nil_append] at hhead0
        rw [hhead0]
        exact hleaf
      have hhalt :
          parserMachine.HaltsWithin steps
            (phaseConfig 4 pad bits log) := by
        unfold TM.HaltsWithin
        rw [hrun]
        exact parserMachine_halts_accept
      have hprefBound :=
        phasePrefixTerminal_le_unit pad hpad head [] log
      have hsteps :
          steps ≤ phaseRuntimeUnit pad log bits := by
        dsimp [steps, hs]
        rw [hshape]
        simpa using hprefBound
      exact parser_terminal_halt_to_budget
        pad log bits steps hsteps hhalt
    · let steps := hs + (log.length + 2)
      rcases leaf_afterEnd_inactive_residual_rejects_exact
          (pad + head.encode.length)
          tail htail log log' hpop hzero with
        ⟨cfg, hleaf, hhaltCfg, _⟩
      have hhalt :
          parserMachine.HaltsWithin steps
            (phaseConfig 4 pad bits log) := by
        unfold TM.HaltsWithin
        dsimp [steps, hs]
        rw [MachineRunLemmas.run_add, hhead, hleaf]
        exact hhaltCfg
      have hprefBound :=
        phasePrefixTerminal_le_unit pad hpad head tail log
      have hsteps :
          steps ≤ phaseRuntimeUnit pad log bits := by
        dsimp [steps, hs]
        rw [hshape]
        simpa using hprefBound
      exact parser_terminal_halt_to_budget
        pad log bits steps hsteps hhalt
  · by_cases htail : tail = []
    · subst tail
      let steps := hs + (log.length + 2)
      rcases leaf_afterEnd_active_exhausted_rejects_exact
          (pad + head.encode.length) (by omega)
          log log' hpop hzero with ⟨right, hleaf⟩
      have hrun :
          parserMachine.run steps (phaseConfig 4 pad bits log) =
            CanonicalSATParserLeafSourceProof.leafRejectConfig
              (pad + head.encode.length) right := by
        dsimp [steps, hs]
        rw [MachineRunLemmas.run_add]
        have hhead0 := hhead
        simp only [List.length_nil, List.reverse_nil, List.map_nil,
          List.nil_append] at hhead0
        rw [hhead0]
        exact hleaf
      have hhalt :
          parserMachine.HaltsWithin steps
            (phaseConfig 4 pad bits log) := by
        unfold TM.HaltsWithin
        rw [hrun]
        exact parserMachine_halts_reject
      have hprefBound :=
        phasePrefixTerminal_le_unit pad hpad head [] log
      have hsteps :
          steps ≤ phaseRuntimeUnit pad log bits := by
        dsimp [steps, hs]
        rw [hshape]
        simpa using hprefBound
      exact parser_terminal_halt_to_budget
        pad log bits steps hsteps hhalt
    · have hchild' := hchild log' hpop hzero htail
      let k := (log.length + 1) + (tail.length + 1)
      let steps := hs + k
      have hleaf :=
        leaf_afterEnd_roundtrip_any_nonempty_active_exact
          (pad + head.encode.length) (by omega)
          tail htail log log' hpop hzero
      have hpref :
          ConfigRightBlankEq
            (parserMachine.run steps
              (phaseConfig 4 pad bits log))
            (phaseConfig 4
              (pad + head.encode.length) tail log') := by
        dsimp [steps, k, hs]
        rw [MachineRunLemmas.run_add, hhead]
        exact hleaf
      have hscale :
          phaseRuntimeScale
              (pad + head.encode.length) log' tail =
            phaseRuntimeScale pad log bits := by
        rw [hshape]
        exact phaseRuntimeScale_pop_same
          pad head tail log log' hpop
      have hprefBound0 :=
        phasePrefixLinear_le_unit pad hpad head tail log
      have hprefBound :
          steps ≤ phaseRuntimeUnit pad log bits := by
        dsimp [steps, k, hs]
        rw [hshape]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hprefBound0
      exact parser_compose_same_scale_rightBlank_to_budget
        pad (pad + head.encode.length)
        log log' bits tail steps hlt hscale hprefBound hpref hchild'


/-- Generic bounded binary phase. AND and OR differ only in their already
certified concrete roundtrip theorem. -/
theorem binary_head_halts_budget
    (pad : Nat) (log : SlotLog)
    (bits tail : BitString) (head : Head)
    (hpad : 0 < pad)
    (hlt : tail.length < bits.length)
    (hshape : bits = head.encode ++ tail)
    (hconsume : tail.length + 3 ≤ bits.length)
    (hterminal :
      tail = [] →
      parserMachine.run
          (CanonicalSATParserPhaseMacroProof.headWorkFuel
              head 0 log.length +
            (log.length + 2))
          (phaseConfig 4 pad bits log) =
        CanonicalSATParserLeafSourceProof.leafRejectConfig
          (pad + head.encode.length)
          ((pushSlot log).map some))
    (hroundtrip :
      tail ≠ [] →
      parserMachine.run
          (CanonicalSATParserPhaseMacroProof.headWorkFuel
              head tail.length log.length +
            (log.length + tail.length + 2))
          (phaseConfig 4 pad bits log) =
        phaseConfig 4
          (pad + head.encode.length) tail (pushSlot log))
    (hchild :
      tail ≠ [] →
      parserMachine.HaltsWithin
        (phaseRuntimeBudget
          (pad + head.encode.length) (pushSlot log) tail)
        (phaseConfig 4
          (pad + head.encode.length) tail (pushSlot log))) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget pad log bits)
      (phaseConfig 4 pad bits log) := by
  by_cases htail : tail = []
  · let steps :=
      CanonicalSATParserPhaseMacroProof.headWorkFuel
          head 0 log.length +
        (log.length + 2)
    have hrun := hterminal htail
    have hhalt :
        parserMachine.HaltsWithin steps
          (phaseConfig 4 pad bits log) := by
      unfold TM.HaltsWithin
      dsimp [steps]
      rw [hrun]
      exact parserMachine_halts_reject
    have hprefBound0 :=
      phasePrefixTerminal_le_unit pad hpad head [] log
    have hprefBound :
        steps ≤ phaseRuntimeUnit pad log bits := by
      dsimp [steps]
      rw [hshape, htail]
      simpa using hprefBound0
    exact parser_terminal_halt_to_budget
      pad log bits steps hprefBound hhalt
  · let steps :=
      CanonicalSATParserPhaseMacroProof.headWorkFuel
          head tail.length log.length +
        (log.length + tail.length + 2)
    have hpref := hroundtrip htail
    have hchild' := hchild htail
    have hscale :
        phaseRuntimeScale
            (pad + head.encode.length) (pushSlot log) tail =
          phaseRuntimeScale pad log bits + 1 := by
      rw [hshape]
      exact phaseRuntimeScale_push_succ pad head tail log
    have hchildScale :
        tail.length + 1 ≤ phaseRuntimeScale pad log bits := by
      unfold phaseRuntimeScale
      omega
    have hprefBound0 :=
      phasePrefixLinear_le_unit pad hpad head tail log
    have hprefBound :
        steps ≤ phaseRuntimeUnit pad log bits := by
      dsimp [steps]
      rw [hshape]
      simpa using hprefBound0
    exact parser_compose_scale_succ_exact_to_budget
      pad (pad + head.encode.length)
      log (pushSlot log) bits tail steps
      hscale hchildScale hconsume hprefBound hpref hchild'


/-- Bounded global parser execution.  Every concrete parser phase halts inside
the explicit quadratic phase budget, with no semantic or endpoint hypothesis. -/
theorem phase_halts_budget_global
    (pad : Nat)
    (log : SlotLog)
    (bits : BitString)
    (hpad : 0 < pad)
    (hactive : activeSlots log ≠ 0) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget pad log bits)
      (phaseConfig 4 pad bits log) := by
  cases hparse : parseHead bits with
  | none =>
      rcases phase_parseHead_none_reject_bound pad bits log hparse with
        ⟨steps, hsteps, hstate⟩
      have hhalt :
          parserMachine.HaltsWithin steps
            (phaseConfig 4 pad bits log) := by
        unfold TM.HaltsWithin
        rw [hstate]
        exact parserMachine_halts_reject
      have hunit :
          bits.length + 1 ≤ phaseRuntimeUnit pad log bits := by
        unfold phaseRuntimeUnit phaseRuntimeScale
        omega
      exact parser_terminal_halt_to_budget
        pad log bits steps (Nat.le_trans hsteps hunit) hhalt
  | some p =>
      rcases p with ⟨head, tail⟩
      have hlt : tail.length < bits.length :=
        parseHead_rest_length_lt hparse
      have hshape : bits = head.encode ++ tail :=
        parseHead_inverse bits head tail hparse
      cases head with
      | not =>
          have hchild :=
            phase_halts_budget_global
              (pad + (Head.encode .not).length)
              log tail (by omega) hactive
          have hpref :
              parserMachine.run (Head.encode .not).length
                  (phaseConfig 4 pad bits log) =
                phaseConfig 4
                  (pad + (Head.encode .not).length) tail log := by
            rw [hshape]
            exact CanonicalSATParserPhaseMacroProof.not_head_roundtrip
              pad tail log
          have hscale :
              phaseRuntimeScale
                  (pad + (Head.encode .not).length) log tail =
                phaseRuntimeScale pad log bits := by
            rw [hshape]
            exact phaseRuntimeScale_same pad Head.not tail log
          have hprefBound0 :=
            phasePrefixNot_le_unit pad hpad tail log
          have hprefBound :
              (Head.encode .not).length ≤
                phaseRuntimeUnit pad log bits := by
            rw [hshape]
            exact hprefBound0
          exact parser_compose_same_scale_exact_to_budget
            pad (pad + (Head.encode .not).length)
            log log bits tail (Head.encode .not).length
            hlt hscale hprefBound hpref hchild
      | and =>
          have hconsume : tail.length + 3 ≤ bits.length := by
            rw [hshape]
            simp [Head.encode]
          apply binary_head_halts_budget
            pad log bits tail Head.and hpad hlt hshape hconsume
          · intro htail
            rw [hshape, htail]
            simpa using
              (CanonicalSATParserBinaryHeadProof.and_head_exhausted_rejects
                pad hpad log)
          · intro htail
            rw [hshape]
            exact and_head_roundtrip_any_nonempty_exact
              pad hpad tail htail log
          · intro htail
            have hpush : activeSlots (pushSlot log) ≠ 0 := by
              rw [activeSlots_pushSlot]
              omega
            exact phase_halts_budget_global
              (pad + (Head.encode .and).length)
              (pushSlot log) tail (by omega) hpush
      | or =>
          have hconsume : tail.length + 3 ≤ bits.length := by
            rw [hshape]
            simp [Head.encode]
          apply binary_head_halts_budget
            pad log bits tail Head.or hpad hlt hshape hconsume
          · intro htail
            rw [hshape, htail]
            simpa using
              (CanonicalSATParserBinaryHeadProof.or_head_exhausted_rejects
                pad hpad log)
          · intro htail
            rw [hshape]
            exact or_head_roundtrip_any_nonempty_exact
              pad hpad tail htail log
          · intro htail
            have hpush : activeSlots (pushSlot log) ≠ 0 := by
              rw [activeSlots_pushSlot]
              omega
            exact phase_halts_budget_global
              (pad + (Head.encode .or).length)
              (pushSlot log) tail (by omega) hpush
      | input i =>
          apply leaf_head_halts_budget
            pad log bits tail (Head.input i)
            hpad hactive hlt hshape
          · rw [hshape]
            exact CanonicalSATParserPhaseMacroProof.input_head_to_pop_search
              pad i tail log
          · intro log' hpop hactive' htail
            exact phase_halts_budget_global
              (pad + (Head.encode (.input i)).length)
              log' tail (by omega) hactive'
      | const b =>
          apply leaf_head_halts_budget
            pad log bits tail (Head.const b)
            hpad hactive hlt hshape
          · rw [hshape]
            exact CanonicalSATParserPhaseMacroProof.const_head_to_pop_search
              pad b tail log
          · intro log' hpop hactive' htail
            exact phase_halts_budget_global
              (pad + (Head.encode (.const b)).length)
              log' tail (by omega) hactive'
termination_by bits.length
decreasing_by
  all_goals exact hlt

#print axioms MCore.Real.P01GlobalParserBound.phase_halts_budget_global


/-- Any two halted fuel snapshots of this deterministic parser are the same
configuration. -/
theorem parser_halted_runs_eq
    (config : Configuration (Fin 25) (Option Bool))
    (m n : Nat)
    (hm :
      parserMachine.halting
        (parserMachine.run m config).state = true)
    (hn :
      parserMachine.halting
        (parserMachine.run n config).state = true) :
    parserMachine.run m config =
      parserMachine.run n config := by
  rcases Nat.le_total m n with hmn | hnm
  · have h :=
      MachineRunLemmas.run_to_larger_fuel_of_halt
        parserMachine config (parserMachine.run m config)
        hmn rfl hm
    exact h.symm
  · exact
      MachineRunLemmas.run_to_larger_fuel_of_halt
        parserMachine config (parserMachine.run n config)
        hnm rfl hn

/-- The fixed quadratic phase fuel realizes the same Boolean semantics as the
existential semantic induction. -/
theorem phase_correct_at_budget
    (pad : Nat)
    (log : SlotLog)
    (bits : BitString)
    (hpad : 0 < pad)
    (hactive : activeSlots log ≠ 0) :
    parserAccepting
        (parserMachine.run
          (phaseRuntimeBudget pad log bits)
          (phaseConfig 4 pad bits log)).state = true ↔
      CanonicalSATParserGlobalSpec.logParseCore
        (bits.length + 1) log bits = true := by
  rcases phaseSemantics_global pad log bits hpad hactive with
    ⟨steps, hhaltSem, hcorrectSem⟩
  have hhaltBudget :=
    phase_halts_budget_global pad log bits hpad hactive
  have heq :=
    parser_halted_runs_eq
      (phaseConfig 4 pad bits log)
      (phaseRuntimeBudget pad log bits) steps
      hhaltBudget hhaltSem
  rw [heq]
  exact hcorrectSem

/-- Initial phase semantics at the canonical one-slot log. -/
theorem phase_initial_accepts_iff_slotAccept
    (bits : BitString) :
    parserAccepting
        (parserMachine.run
          (phaseRuntimeBudget 1 initialSlotLog bits)
          (phaseConfig 4 1 bits initialSlotLog)).state = true ↔
      slotAccept bits = true := by
  exact
    (phase_correct_at_budget
      1 initialSlotLog bits (by decide) (by decide)).trans
      (CanonicalSATParserGlobalSpec.logAccept_iff_slotAccept bits)

/-- Exact proof-side total fuel: deterministic initialization plus the bounded
global parser phase. -/
def parserProofBudget (bits : BitString) : Nat :=
  2 * bits.length + 4 +
    phaseRuntimeBudget 1 initialSlotLog bits

theorem parserProofBudget_le_parserTimeBound
    (bits : BitString) :
    parserProofBudget bits ≤ parserTimeBound bits.length := by
  let n := bits.length
  have hs : n + 3 ≤ 3 * (n + 1) := by omega
  have hu0 := Nat.mul_le_mul_left 16 hs
  have hu :
      16 * (n + 3) ≤ 48 * (n + 1) := by
    calc
      16 * (n + 3) ≤ 16 * (3 * (n + 1)) := hu0
      _ = 48 * (n + 1) := by
        rw [← Nat.mul_assoc]
  have hp :=
    Nat.mul_le_mul_right (n + 1) hu
  have hone : 1 ≤ n + 1 := by omega
  have hsq0 := Nat.mul_le_mul_left (n + 1) hone
  have hsq : n + 1 ≤ (n + 1) * (n + 1) := by
    simpa using hsq0
  have hi0 : 2 * n + 4 ≤ 4 * (n + 1) := by omega
  have hi1 := Nat.mul_le_mul_left 4 hsq
  have hi :
      2 * n + 4 ≤ 4 * ((n + 1) * (n + 1)) :=
    Nat.le_trans hi0 hi1
  have hsum :=
    Nat.add_le_add hi hp
  have h52 :
      4 * ((n + 1) * (n + 1)) +
          48 * ((n + 1) * (n + 1)) =
        52 * ((n + 1) * (n + 1)) := by
    calc
      4 * ((n + 1) * (n + 1)) +
          48 * ((n + 1) * (n + 1)) =
        (4 + 48) * ((n + 1) * (n + 1)) :=
          (Nat.add_mul 4 48 ((n + 1) * (n + 1))).symm
      _ = 52 * ((n + 1) * (n + 1)) := by rfl
  have hcoef : 52 ≤ 256 := by omega
  have hfinal :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) hcoef
  unfold parserProofBudget parserTimeBound
  unfold phaseRuntimeBudget phaseRuntimeUnit phaseRuntimeScale
  simp only [initialSlotLog, List.length_cons, List.length_nil]
  change
    2 * n + 4 + (16 * (1 + n + 1 + 1) * (n + 1)) ≤
      256 * (n + 1) ^ 2
  have hphaseShape :
      16 * (1 + n + 1 + 1) * (n + 1) =
        16 * (n + 3) * (n + 1) := by
    congr 2 <;> omega
  rw [hphaseShape]
  have hsum' :
      2 * n + 4 + (16 * (n + 3) * (n + 1)) ≤
        4 * ((n + 1) * (n + 1)) +
          48 * ((n + 1) * (n + 1)) := by
    simpa [Nat.mul_assoc] using hsum
  calc
    2 * n + 4 + (16 * (n + 3) * (n + 1))
        ≤ 4 * ((n + 1) * (n + 1)) +
          48 * ((n + 1) * (n + 1)) := hsum'
    _ = 52 * ((n + 1) * (n + 1)) := h52
    _ ≤ 256 * ((n + 1) * (n + 1)) := hfinal
    _ = 256 * (n + 1) ^ 2 := by
      simp [Nat.pow_succ, Nat.mul_assoc]


/-- Deterministic initializer reaches the exact phase-4 one-slot configuration. -/
theorem parser_initializes_to_phase
    (bits : BitString) :
    parserMachine.run (2 * bits.length + 4)
        (initialTMConfig parserMachine bits) =
      phaseConfig 4 1 bits initialSlotLog := by
  simpa using
    (CanonicalSATParserInitProof.parser_initializes bits)

/-- The complete proof-side execution halts before its exact composite budget. -/
theorem parserProofBudget_halts
    (bits : BitString) :
    parserMachine.HaltsWithin
      (parserProofBudget bits)
      (initialTMConfig parserMachine bits) := by
  unfold parserProofBudget TM.HaltsWithin
  rw [MachineRunLemmas.run_add]
  rw [parser_initializes_to_phase]
  exact
    phase_halts_budget_global
      1 initialSlotLog bits (by decide) (by decide)

/-- The exact composite proof-side fuel realizes slotAccept. -/
theorem parserProofBudget_accepts_iff
    (bits : BitString) :
    parserAccepting
        (parserMachine.run
          (parserProofBudget bits)
          (initialTMConfig parserMachine bits)).state = true ↔
      slotAccept bits = true := by
  unfold parserProofBudget
  rw [MachineRunLemmas.run_add]
  rw [parser_initializes_to_phase]
  exact phase_initial_accepts_iff_slotAccept bits

/-- Total halting promoted from the proof-side budget to the repository's fixed
polynomial parserTimeBound. -/
theorem parser_halts_within_timeBound
    (bits : BitString) :
    parserMachine.HaltsWithin
      (parserTimeBound bits.length)
      (initialTMConfig parserMachine bits) := by
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine
    (initialTMConfig parserMachine bits)
    (parserProofBudget_le_parserTimeBound bits)
    (parserProofBudget_halts bits)

/-- Semantic correctness at the exact fixed parserTimeBound fuel. -/
theorem parser_realizes_slotAccept_at_timeBound
    (bits : BitString) :
    parserAccepting
        (parserMachine.run
          (parserTimeBound bits.length)
          (initialTMConfig parserMachine bits)).state = true ↔
      slotAccept bits = true := by
  have hhalt := parserProofBudget_halts bits
  have hrun :=
    MachineRunLemmas.run_to_larger_fuel_of_halt
      parserMachine
      (initialTMConfig parserMachine bits)
      (parserMachine.run
        (parserProofBudget bits)
        (initialTMConfig parserMachine bits))
      (parserProofBudget_le_parserTimeBound bits)
      rfl
      hhalt
  rw [hrun]
  exact parserProofBudget_accepts_iff bits

/-- T1.1 terminal product: a no-hypothesis global simulation certificate for
the concrete Fin-25 parser machine. -/
theorem slot_parser_machine_simulation_certificate :
    CanonicalSATRecursiveParserSimulation.SlotParserMachineSimulationCertificate :=
  { halts := parser_halts_within_timeBound
    realizes_slotAccept := parser_realizes_slotAccept_at_timeBound }

#print axioms MCore.Real.P01GlobalParserBound.parser_initializes_to_phase
#print axioms MCore.Real.P01GlobalParserBound.parserProofBudget_halts
#print axioms MCore.Real.P01GlobalParserBound.parserProofBudget_accepts_iff
#print axioms MCore.Real.P01GlobalParserBound.parser_halts_within_timeBound
#print axioms MCore.Real.P01GlobalParserBound.parser_realizes_slotAccept_at_timeBound
#print axioms MCore.Real.P01GlobalParserBound.slot_parser_machine_simulation_certificate

#print axioms MCore.Real.P01GlobalParserBound.phase_correct_at_budget
#print axioms MCore.Real.P01GlobalParserBound.parserProofBudget_le_parserTimeBound

#print axioms MCore.Real.P01GlobalParserBound.budget_compose_same_scale
#print axioms MCore.Real.P01GlobalParserBound.budget_compose_scale_succ

end P01GlobalParserBound
end Real
end MCore
