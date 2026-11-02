import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.P01PreservingUnaryPhysicalRuns
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderMaterial

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate
open P01PreservingUnaryPhysicalRuns
open MachineRunLemmas

def preservingUnaryTimeBound : TimeBound :=
  fun n => 16 * (n + 1) ^ 2

theorem preservingUnaryTimeBound_poly :
    PolynomialTimeBound preservingUnaryTimeBound := by
  exact ⟨16, 2, by intro n; exact Nat.le_refl _⟩

theorem encodeNat_length (i : Nat) :
    (encodeNat i).length = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [encodeNat, ih, Nat.add_assoc]

theorem preservingUnaryExactFuel_le_timeBound
    (witness : BitString) (i : Nat)
    (hi : i < witness.length) :
    preservingUnaryExactFuel i ≤
      preservingUnaryTimeBound
        (witness.length + (encodeNat i).length) := by
  have hq := preservingUnaryExactFuel_le_quadratic i
  have hil : i + 1 ≤ witness.length + (encodeNat i).length + 1 := by
    rw [encodeNat_length]
    omega
  have hsq : (i + 1) ^ 2 ≤
      (witness.length + (encodeNat i).length + 1) ^ 2 := by
    exact Nat.pow_le_pow_left hil 2
  unfold preservingUnaryTimeBound
  exact Nat.le_trans hq (Nat.mul_le_mul_left 16 hsq)

theorem preservingUnary_run_timeBound
    (witness : BitString) (i : Nat)
    (hi : i < witness.length) :
    preservingUnaryReadMachine.run
        (preservingUnaryTimeBound
          (witness.length + (encodeNat i).length))
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape witness i } =
      { state := haltState (witness.getD i false)
        tape :=
          { left := List.replicate (i + 2) none ++ witness.map some
            head := none
            right := [] } } := by
  let init : Configuration PreservingReadState (Option Bool) :=
    { state := preservingUnaryReadMachine.initial
      tape := witnessReadTape witness i }
  let done : Configuration PreservingReadState (Option Bool) :=
    { state := haltState (witness.getD i false)
      tape :=
        { left := List.replicate (i + 2) none ++ witness.map some
          head := none
          right := [] } }
  have hexact : preservingUnaryReadMachine.run
      (preservingUnaryExactFuel i) init = done := by
    simpa [init, done] using preservingUnary_run_exact witness i hi
  have hhalt : preservingUnaryReadMachine.halting done.state = true := by
    dsimp [done, haltState]
    cases witness.getD i false <;> rfl
  have hle := preservingUnaryExactFuel_le_timeBound witness i hi
  simpa [init, done] using
    run_to_larger_fuel_of_halt preservingUnaryReadMachine init done hle hexact hhalt

theorem preservingUnary_halts_material :
    ∀ (witness : BitString) (i : Nat),
      i < witness.length →
      preservingUnaryReadMachine.HaltsWithin
        (preservingUnaryTimeBound
          (witness.length + (encodeNat i).length))
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape witness i } := by
  intro witness i hi
  unfold TM.HaltsWithin
  rw [preservingUnary_run_timeBound witness i hi]
  unfold haltState
  cases witness.getD i false <;> rfl

theorem preservingUnary_correct_material :
    ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
      preservingReadAccepting
        (preservingUnaryReadMachine.run
          (preservingUnaryTimeBound
            (witness.length + (encodeNat i).length))
          { state := preservingUnaryReadMachine.initial
            tape := witnessReadTape witness i }).state =
        witness.getD i false := by
  intro witness i hi
  rw [preservingUnary_run_timeBound witness i hi]
  unfold haltState
  cases witness.getD i false <;> rfl

theorem preservingUnary_preserves_material :
    ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
      ∃ left right : List (Option Bool),
        (preservingUnaryReadMachine.run
          (preservingUnaryTimeBound
            (witness.length + (encodeNat i).length))
          { state := preservingUnaryReadMachine.initial
            tape := witnessReadTape witness i }).tape =
          { left := left ++ witness.map some
            head := none
            right := right } := by
  intro witness i hi
  rw [preservingUnary_run_timeBound witness i hi]
  refine ⟨List.replicate (i + 2) none, [], ?_⟩
  rfl

def ConcreteClosureWitnessPreservingUnary :
    PreservingUnaryReaderCertificate :=
  { machine := preservingUnaryReadMachine
    machine_eq := rfl
    accepting := preservingReadAccepting
    accepting_eq := rfl
    timeBound := preservingUnaryTimeBound
    time_poly := preservingUnaryTimeBound_poly
    halts := preservingUnary_halts_material
    correct := preservingUnary_correct_material
    preservesWitness := preservingUnary_preserves_material }

theorem preservingUnaryReaderGap_material :
    PreservingUnaryReaderGap :=
  ⟨ConcreteClosureWitnessPreservingUnary⟩

#print axioms MCore.Real.P01PreservingUnaryReaderMaterial.ConcreteClosureWitnessPreservingUnary
#print axioms MCore.Real.P01PreservingUnaryReaderMaterial.preservingUnaryReaderGap_material

end P01PreservingUnaryReaderMaterial
end Real
end MCore
