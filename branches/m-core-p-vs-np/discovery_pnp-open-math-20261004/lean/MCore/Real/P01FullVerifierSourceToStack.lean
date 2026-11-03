import MCore.Real.P01FullVerifierTraversal
import MCore.Real.P01FullVerifierPhysicalStackV2

namespace MCore
namespace Real
namespace P01FullVerifierSourceToStack

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierTraversal
open P01FullVerifierPhysicalShuttles
open P01FullVerifierPhysicalStackV2

/-- Exact physical entry invariant for a nonempty canonical source:
the certified fixed scanner reaches the source-end blank, and one primitive
right move enters the canonical empty V2 evaluation stack without changing
witness or source. -/
theorem prepared_scan_then_enter_empty_stack
    (witness : BitString) (b : Bool) (bs : BitString) :
    let scanFinal :=
      sourceEndScanner.run ((b :: bs).length + 1)
        { state := sourceEndScanner.initial,
          tape := preparedTape witness (b :: bs) }
    Tape.move none .right scanFinal.tape =
      physicalStackV2Tape witness (b :: bs) [] := by
  dsimp
  rw [preparedTape_eq_scanConfig witness b bs]
  have hrun :=
    sourceEndScanner_run (none :: witness.map some) (b :: bs)
  calc
    Tape.move none .right
        (sourceEndScanner.run ((b :: bs).length + 1)
          (scanConfig (none :: witness.map some) (b :: bs))).tape =
      Tape.move none .right (sourceEndTape witness (b :: bs)) := by
        simpa [sourceEndTape] using
          congrArg (fun cfg => Tape.move none .right cfg.tape) hrun
    _ = physicalStackV2Tape witness (b :: bs) [] :=
      sourceEnd_to_stackV2 witness (b :: bs)

/-- The entry path is polynomial-time before the single stack-entry move. -/
theorem prepared_source_scan_halts_before_stack_entry
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceEndScanner.HaltsWithin ((b :: bs).length + 1)
      { state := sourceEndScanner.initial,
        tape := preparedTape witness (b :: bs) } :=
  prepared_source_scan_halts witness b bs

#print axioms MCore.Real.P01FullVerifierSourceToStack.prepared_scan_then_enter_empty_stack
#print axioms MCore.Real.P01FullVerifierSourceToStack.prepared_source_scan_halts_before_stack_entry

end P01FullVerifierSourceToStack
end Real
end MCore
