import MCore.Real.CanonicalSATParserHeadProof
import MCore.Real.CanonicalSATParserMacroProof
import MCore.Real.CanonicalSATParserReturnProof

namespace MCore
namespace Real
namespace CanonicalSATParserPhaseMacroProof

open CanonicalFinalProof
open CanonicalSATSlotParserSpec
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserMacroProof
open CanonicalSATParserWorkScanProof
open CanonicalSATSlotLog
open MachineRunLemmas

/-- Composite fuel for one decoded head followed by the already-certified
source/work-log macro. Keeping the sum behind a named definition avoids
elaboration ambiguity while preserving the exact runtime decomposition. -/
def headWorkFuel (head : Head) (tailLength logLength : Nat) : Nat :=
  head.encode.length + phaseWorkBound tailLength logLength

/-- INPUT head consumption followed by the certified leaf seek/work scan. -/
theorem input_head_to_pop_search
    (pad i : Nat)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel (Head.input i) tail.length log.length)
        (phaseConfig 4 pad (Head.encode (.input i) ++ tail) log) =
      afterEndMoveLeft 13
        (none :: tail.reverse.map some ++
          List.replicate (pad + (Head.encode (.input i)).length)
            (none : Option Bool))
        log none := by
  unfold headWorkFuel phaseWorkBound
  rw [MachineRunLemmas.run_add]
  rw [consumeHead_run]
  simpa [continuationState] using
    (leaf_phase_to_pop_search
      (pad + (Head.encode (.input i)).length) tail log)

/-- Constant head consumption followed by the certified leaf seek/work scan. -/
theorem const_head_to_pop_search
    (pad : Nat)
    (b : Bool)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel (Head.const b) tail.length log.length)
        (phaseConfig 4 pad (Head.encode (.const b) ++ tail) log) =
      afterEndMoveLeft 13
        (none :: tail.reverse.map some ++
          List.replicate (pad + (Head.encode (.const b)).length)
            (none : Option Bool))
        log none := by
  unfold headWorkFuel phaseWorkBound
  rw [MachineRunLemmas.run_add]
  rw [consumeHead_run]
  simpa [continuationState] using
    (leaf_phase_to_pop_search
      (pad + (Head.encode (.const b)).length) tail log)

/-- Unary NOT is already a complete phase-to-phase macro: its slot count and
physical log are unchanged. -/
theorem not_head_roundtrip
    (pad : Nat)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run (Head.encode .not).length
        (phaseConfig 4 pad (Head.encode .not ++ tail) log) =
      phaseConfig 4
        (pad + (Head.encode .not).length) tail log := by
  simpa [continuationState] using
    (consumeHead_run pad Head.not tail log)

/-- AND head consumption followed by the certified binary seek/work append. -/
theorem and_head_to_return
    (pad : Nat)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.and tail.length log.length)
        (phaseConfig 4 pad (Head.encode .and ++ tail) log) =
      afterEndMoveLeft 20
        (none :: tail.reverse.map some ++
          List.replicate (pad + (Head.encode .and).length)
            (none : Option Bool))
        log (some true) := by
  unfold headWorkFuel phaseWorkBound
  rw [MachineRunLemmas.run_add]
  rw [consumeHead_run]
  simpa [continuationState] using
    (binary_phase_to_return
      (pad + (Head.encode .and).length) tail log)

/-- OR head consumption followed by the certified binary seek/work append. -/
theorem or_head_to_return
    (pad : Nat)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.or tail.length log.length)
        (phaseConfig 4 pad (Head.encode .or ++ tail) log) =
      afterEndMoveLeft 20
        (none :: tail.reverse.map some ++
          List.replicate (pad + (Head.encode .or).length)
            (none : Option Bool))
        log (some true) := by
  unfold headWorkFuel phaseWorkBound
  rw [MachineRunLemmas.run_add]
  rw [consumeHead_run]
  simpa [continuationState] using
    (binary_phase_to_return
      (pad + (Head.encode .or).length) tail log)

#print axioms MCore.Real.CanonicalSATParserPhaseMacroProof.input_head_to_pop_search
#print axioms MCore.Real.CanonicalSATParserPhaseMacroProof.const_head_to_pop_search
#print axioms MCore.Real.CanonicalSATParserPhaseMacroProof.not_head_roundtrip
#print axioms MCore.Real.CanonicalSATParserPhaseMacroProof.and_head_to_return
#print axioms MCore.Real.CanonicalSATParserPhaseMacroProof.or_head_to_return

end CanonicalSATParserPhaseMacroProof
end Real
end MCore
