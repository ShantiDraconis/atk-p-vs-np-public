import MCore.Real.CanonicalSATParserWorkScanProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserRewindProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserInitProof
open CanonicalSATParserHeadProof
open CanonicalSATSlotLog

/-- State-22 configuration while rewinding unread source. remaining is ordered
from current head toward the left boundary; processed is the suffix already
crossed while moving left. The work log remains behind the blank delimiter. -/
def rewindUnreadConfig
    (remaining processed : BitString)
    (leftBlankCount : Nat)
    (log : SlotLog) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 22
        tape :=
          { left := List.replicate leftBlankCount.pred none
            head := none
            right := processed.map some ++ none :: log.map some } }
  | b :: bs =>
      { state := 22
        tape :=
          { left := bs.map some ++ List.replicate leftBlankCount none
            head := some b
            right := processed.map some ++ none :: log.map some } }

@[simp] theorem rewindUnreadConfig_state
    (remaining processed : BitString)
    (leftBlankCount : Nat)
    (log : SlotLog) :
    (rewindUnreadConfig remaining processed leftBlankCount log).state =
      (22 : Fin 25) := by
  cases remaining <;> rfl

@[simp] theorem parser_not_halted_22 :
    parserMachine.halting (22 : Fin 25) = false := by decide

theorem rewindUnread_step_cons
    (b : Bool)
    (bs processed : BitString)
    (leftBlankCount : Nat)
    (log : SlotLog) :
    parserMachine.step
      (rewindUnreadConfig (b :: bs) processed leftBlankCount log) =
    rewindUnreadConfig bs (b :: processed) leftBlankCount log := by
  cases bs <;> cases leftBlankCount <;>
    simp [rewindUnreadConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc, List.replicate_succ]

theorem rewindUnread_finish
    (processed : BitString)
    (leftBlankCount : Nat)
    (hpos : 0 < leftBlankCount)
    (log : SlotLog) :
    parserMachine.step
      (rewindUnreadConfig [] processed leftBlankCount log) =
    phaseConfig 4 leftBlankCount processed log := by
  cases leftBlankCount with
  | zero => omega
  | succ n =>
      cases processed <;>
        simp [rewindUnreadConfig, phaseConfig, parserMachine,
          TM.step, Tape.write, Tape.move, List.replicate_succ,
          List.map_append, List.append_assoc]

theorem rewindUnread_run
    (remaining processed : BitString)
    (leftBlankCount : Nat)
    (hpos : 0 < leftBlankCount)
    (log : SlotLog) :
    parserMachine.run (remaining.length + 1)
      (rewindUnreadConfig remaining processed leftBlankCount log) =
    phaseConfig 4 leftBlankCount
      (remaining.reverse ++ processed) log := by
  induction remaining generalizing processed with
  | nil =>
      simpa using rewindUnread_finish processed leftBlankCount hpos log
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, rewindUnreadConfig_state, parser_not_halted_22]
      rw [rewindUnread_step_cons]
      rw [ih (b :: processed)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewindUnread_from_reverse
    (unread : BitString)
    (leftBlankCount : Nat)
    (hpos : 0 < leftBlankCount)
    (log : SlotLog) :
    parserMachine.run (unread.length + 1)
      (rewindUnreadConfig unread.reverse [] leftBlankCount log) =
    phaseConfig 4 leftBlankCount unread log := by
  have h := rewindUnread_run unread.reverse [] leftBlankCount hpos log
  simpa using h

#print axioms MCore.Real.CanonicalSATParserRewindProof.rewindUnread_step_cons
#print axioms MCore.Real.CanonicalSATParserRewindProof.rewindUnread_run
#print axioms MCore.Real.CanonicalSATParserRewindProof.rewindUnread_from_reverse

end CanonicalSATParserRewindProof
end Real
end MCore
