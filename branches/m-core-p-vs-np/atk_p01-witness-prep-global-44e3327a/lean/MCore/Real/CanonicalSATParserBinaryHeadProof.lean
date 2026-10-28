import MCore.Real.CanonicalSATParserPhaseMacroProof
import MCore.Real.CanonicalSATParserTerminalBranches

namespace MCore
namespace Real
namespace CanonicalSATParserBinaryHeadProof

open CanonicalFinalProof
open CanonicalSATSlotParserSpec
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserWorkScanProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserPhaseMacroProof
open CanonicalSATParserReturnProof
open CanonicalSATParserTerminalBranches
open CanonicalSATSlotLog
open MachineRunLemmas

/-- Complete AND macro when unread source remains.  The parameterization
`rest.reverse ++ [last]` is exactly the source shape expected by the certified
rewind theorem and covers every nonempty bitstring. -/
theorem and_head_roundtrip_nonempty
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.and (rest.reverse ++ [last]).length log.length +
          (log.length + 2 + (rest.length + 1)))
        (phaseConfig 4 pad
          (Head.encode .and ++ (rest.reverse ++ [last])) log) =
      phaseConfig 4
        (pad + (Head.encode .and).length)
        (rest.reverse ++ [last])
        (pushSlot log) := by
  rw [MachineRunLemmas.run_add]
  rw [and_head_to_return]
  simpa using
    (binary_afterEnd_roundtrip
      (pad + (Head.encode .and).length)
      (by omega)
      last rest log)

/-- Complete OR macro when unread source remains. -/
theorem or_head_roundtrip_nonempty
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.or (rest.reverse ++ [last]).length log.length +
          (log.length + 2 + (rest.length + 1)))
        (phaseConfig 4 pad
          (Head.encode .or ++ (rest.reverse ++ [last])) log) =
      phaseConfig 4
        (pad + (Head.encode .or).length)
        (rest.reverse ++ [last])
        (pushSlot log) := by
  rw [MachineRunLemmas.run_add]
  rw [or_head_to_return]
  simpa using
    (binary_afterEnd_roundtrip
      (pad + (Head.encode .or).length)
      (by omega)
      last rest log)

/-- AND has arity two, so an exhausted source after its head is malformed and
must reject. -/
theorem and_head_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.and 0 log.length + (log.length + 2))
        (phaseConfig 4 pad (Head.encode .and) log) =
      leafRejectConfig
        (pad + (Head.encode .and).length)
        ((pushSlot log).map some) := by
  rw [MachineRunLemmas.run_add]
  have hHead :
      parserMachine.run (headWorkFuel Head.and 0 log.length)
          (phaseConfig 4 pad (Head.encode .and) log) =
        afterEndMoveLeft 20
          (none :: List.replicate (pad + (Head.encode .and).length)
            (none : Option Bool))
          log (some true) := by
    simpa using
      (and_head_to_return pad ([] : BitString) log)
  rw [hHead]
  rw [MachineRunLemmas.run_add]
  rw [binary_afterEnd_to_delimiter
    (List.replicate (pad + (Head.encode .and).length)
      (none : Option Bool)) log]
  exact
    binary_exhausted_rejects
      (pad + (Head.encode .and).length)
      (by omega)
      ((pushSlot log).map some)

/-- OR has arity two, so an exhausted source after its head is malformed and
must reject. -/
theorem or_head_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (log : SlotLog) :
    parserMachine.run
        (headWorkFuel Head.or 0 log.length + (log.length + 2))
        (phaseConfig 4 pad (Head.encode .or) log) =
      leafRejectConfig
        (pad + (Head.encode .or).length)
        ((pushSlot log).map some) := by
  rw [MachineRunLemmas.run_add]
  have hHead :
      parserMachine.run (headWorkFuel Head.or 0 log.length)
          (phaseConfig 4 pad (Head.encode .or) log) =
        afterEndMoveLeft 20
          (none :: List.replicate (pad + (Head.encode .or).length)
            (none : Option Bool))
          log (some true) := by
    simpa using
      (or_head_to_return pad ([] : BitString) log)
  rw [hHead]
  rw [MachineRunLemmas.run_add]
  rw [binary_afterEnd_to_delimiter
    (List.replicate (pad + (Head.encode .or).length)
      (none : Option Bool)) log]
  exact
    binary_exhausted_rejects
      (pad + (Head.encode .or).length)
      (by omega)
      ((pushSlot log).map some)

#print axioms MCore.Real.CanonicalSATParserBinaryHeadProof.and_head_roundtrip_nonempty
#print axioms MCore.Real.CanonicalSATParserBinaryHeadProof.or_head_roundtrip_nonempty
#print axioms MCore.Real.CanonicalSATParserBinaryHeadProof.and_head_exhausted_rejects
#print axioms MCore.Real.CanonicalSATParserBinaryHeadProof.or_head_exhausted_rejects

end CanonicalSATParserBinaryHeadProof
end Real
end MCore
