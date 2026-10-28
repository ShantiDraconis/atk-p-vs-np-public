import MCore.Real.P01FullVerifierSourceRewind
import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01FullVerifierSourceRoundTrip

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalShuttles
open P01FullVerifierSourceRewind
open MachineRunLemmas

/-- Exact physical rewind invariant for every nonempty canonical source.
Starting at the source-end blank, the fixed rewind TM restores precisely the
prepared witness/source layout, preserving both bitstrings. -/
theorem sourceRewind_run_to_prepared_nonempty
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource,
        tape := sourceEndTape witness (b :: bs) } =
      { state := rewindHalt,
        tape := preparedTape witness (b :: bs) } := by
  rw [show (b :: bs).length + 2 =
      1 + ((b :: bs).length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  rw [sourceRewind_run_one_enter]
  rw [show (b :: bs).length + 1 =
      (b :: bs).reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [rewind_scan_run]
  simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.run, TM.step, Tape.write, Tape.move,
    P01WitnessPreservingPrep.preparedTape]

#print axioms MCore.Real.P01FullVerifierSourceRoundTrip.sourceRewind_run_to_prepared_nonempty

end P01FullVerifierSourceRoundTrip
end Real
end MCore
