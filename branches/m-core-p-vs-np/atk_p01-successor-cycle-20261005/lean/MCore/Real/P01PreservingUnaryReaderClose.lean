import MCore.Real.P01PreservingUnaryUniversalRun

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderClose

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate
open P01PreservingUnaryReaderBound
open P01PreservingUnaryUniversalRun
open P01PreservingUnaryRewind
open MachineRunLemmas

private def readerStart (witness : BitString) (i : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := preservingUnaryReadMachine.initial
    tape := P01WitnessIndexedRead.witnessReadTape witness i }

private def readerBound (witness : BitString) (i : Nat) : Nat :=
  preservingUnaryReaderTimeBound (witness.length + (encodeNat i).length)

theorem reader_exact_material
    (witness : BitString) (i : Nat) (hi : i < witness.length) :
    ∃ b leftBlanks,
      b = witness.getD i false ∧
      preservingUnaryReadMachine.run (readerBound witness i)
        (readerStart witness i) = haltedConfig b witness leftBlanks := by
  cases i with
  | zero =>
      cases witness with
      | nil => simp at hi
      | cons b tail =>
          refine ⟨b, 2, ?_, ?_⟩
          · simp
          · have h5 := preservingRead_zero_run_five b tail
            have hbound := zeroFuel_le_timeBound (b :: tail)
            have hhalt :
                preservingUnaryReadMachine.halting
                  ({ state := if b then PreservingReadState.haltTrue
                       else PreservingReadState.haltFalse
                     tape := zeroDoneTape (b :: tail) } :
                    Configuration PreservingReadState (Option Bool)).state = true := by
              cases b <;> rfl
            have hrun := run_to_larger_fuel_of_halt
              preservingUnaryReadMachine (readerStart (b :: tail) 0)
              ({ state := if b then PreservingReadState.haltTrue
                   else PreservingReadState.haltFalse
                 tape := zeroDoneTape (b :: tail) } :
                Configuration PreservingReadState (Option Bool))
              hbound h5 hhalt
            simpa [readerBound, readerStart, haltedConfig, zeroDoneTape,
              List.replicate_succ] using hrun
  | succ j =>
      obtain ⟨fuel, b, blanks, hle, hbit, hrun⟩ :=
        preservingRead_nonzero_material witness (j + 1) (by omega) hi
      refine ⟨b, blanks, hbit, ?_⟩
      have hhalt :
          preservingUnaryReadMachine.halting (haltedConfig b witness blanks).state = true := by
        cases b <;> rfl
      have hfull := run_to_larger_fuel_of_halt
        preservingUnaryReadMachine (readerStart witness (j + 1))
        (haltedConfig b witness blanks) hle hrun hhalt
      simpa [readerBound, readerStart] using hfull

theorem reader_certificate : PreservingUnaryReaderGap := by
  refine ⟨{
    machine := preservingUnaryReadMachine
    machine_eq := rfl
    accepting := preservingReadAccepting
    accepting_eq := rfl
    timeBound := preservingUnaryReaderTimeBound
    time_poly := preservingUnaryReaderTimeBound_poly
    halts := ?_
    correct := ?_
    preservesWitness := ?_
  }⟩
  · intro witness i hi
    obtain ⟨b, blanks, hbit, hrun⟩ := reader_exact_material witness i hi
    unfold TM.HaltsWithin
    change preservingUnaryReadMachine.halting
      (preservingUnaryReadMachine.run (readerBound witness i) (readerStart witness i)).state = true
    rw [hrun]
    cases b <;> rfl
  · intro witness i hi
    obtain ⟨b, blanks, hbit, hrun⟩ := reader_exact_material witness i hi
    change preservingReadAccepting
      (preservingUnaryReadMachine.run (readerBound witness i) (readerStart witness i)).state = witness.getD i false
    rw [hrun]
    cases b <;> first | exact hbit | (simp only [haltedConfig, preservingReadAccepting, ite_true, ite_false]; exact hbit)
  · intro witness i hi
    obtain ⟨b, blanks, hbit, hrun⟩ := reader_exact_material witness i hi
    refine ⟨List.replicate blanks none, [], ?_⟩
    change (preservingUnaryReadMachine.run (readerBound witness i)
      (readerStart witness i)).tape =
      { left := List.replicate blanks none ++ witness.map some, head := none, right := [] }
    rw [hrun]
    rfl

#print axioms MCore.Real.P01PreservingUnaryReaderClose.reader_certificate

end P01PreservingUnaryReaderClose
end Real
end MCore
