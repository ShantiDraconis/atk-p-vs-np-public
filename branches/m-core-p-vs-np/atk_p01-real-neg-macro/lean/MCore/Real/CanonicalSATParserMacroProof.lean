import MCore.Real.CanonicalSATParserWorkScanProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserMacroProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserWorkScanProof
open CanonicalSATSlotLog
open CanonicalSATSlotLogMachine

/-- Compose the already-proved source seek with the work-log scan for a leaf.
This reaches the exact state-13 pop-search configuration from the parser phase
state 11, without introducing a second parser semantics. -/
theorem leaf_phase_to_pop_search
    (pad : Nat)
    (unread : BitString)
    (log : SlotLog) :
    parserMachine.run
        ((unread.length + 1) + (log.length + 1))
        (phaseConfig 11 pad unread log) =
      afterEndMoveLeft 13
        (none :: unread.reverse.map some ++
          List.replicate pad (none : Option Bool))
        log none := by
  have hphase :
      phaseConfig 11 pad unread log =
        sourceScanConfig 11
          (List.replicate pad (none : Option Bool)) unread log := by
    cases unread <;> rfl
  rw [hphase]
  rw [MachineRunLemmas.run_add]
  rw [leaf_seek_to_work]
  rw [leaf_scan_log_to_pop]

/-- Compose the already-proved source seek with the binary work-log append.
This reaches the exact state-20 return configuration after appending the new
active slot created by AND/OR. -/
theorem binary_phase_to_return
    (pad : Nat)
    (unread : BitString)
    (log : SlotLog) :
    parserMachine.run
        ((unread.length + 1) + (log.length + 1))
        (phaseConfig 18 pad unread log) =
      afterEndMoveLeft 20
        (none :: unread.reverse.map some ++
          List.replicate pad (none : Option Bool))
        log (some true) := by
  have hphase :
      phaseConfig 18 pad unread log =
        sourceScanConfig 18
          (List.replicate pad (none : Option Bool)) unread log := by
    cases unread <;> rfl
  rw [hphase]
  rw [MachineRunLemmas.run_add]
  rw [binary_seek_to_work]
  rw [binary_scan_log_to_return]

/-- Concrete composite runtime used by the next parser-simulation layer. -/
def phaseWorkBound
    (unreadLength logLength : Nat) : Nat :=
  (unreadLength + 1) + (logLength + 1)

theorem phaseWorkBound_linear
    (unreadLength logLength : Nat) :
    phaseWorkBound unreadLength logLength =
      unreadLength + logLength + 2 := by
  simp [phaseWorkBound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

#print axioms MCore.Real.CanonicalSATParserMacroProof.leaf_phase_to_pop_search
#print axioms MCore.Real.CanonicalSATParserMacroProof.binary_phase_to_return
#print axioms MCore.Real.CanonicalSATParserMacroProof.phaseWorkBound_linear

end CanonicalSATParserMacroProof
end Real
end MCore
