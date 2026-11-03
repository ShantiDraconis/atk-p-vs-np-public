import MCore.Real.P01PreservingUnaryIteration
import MCore.Real.P01PreservingUnaryFinalRead
import MCore.Real.P01PreservingUnaryRewind
import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderBound

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryIteration
open P01PreservingUnarySuccessorCycle
open P01PreservingUnaryReaderCertificate

/-- Exact nonzero-path fuel accounting used by the universal reader proof. -/
def nonzeroReaderFuel (i : Nat) : Nat :=
  2 * i ^ 2 + 12 * i + 5

/-- Loose cubic envelope.  The larger constant keeps the arithmetic proof
structural and independent of nonlinear automation. -/
def preservingUnaryReaderTimeBound : TimeBound :=
  fun n => 64 * (n + 1) ^ 3

theorem preservingUnaryReaderTimeBound_poly :
    PolynomialTimeBound preservingUnaryReaderTimeBound := by
  refine ⟨64, 3, ?_⟩
  intro n
  exact Nat.le_refl _

/-- The exact nonzero reader fuel is dominated by the cubic certificate
envelope at the canonical input size. -/
theorem nonzeroReaderFuel_le_timeBound
    (witness : BitString) (i : Nat) :
    nonzeroReaderFuel i ≤
      preservingUnaryReaderTimeBound
        (witness.length + (encodeNat i).length) := by
  let N := witness.length + (encodeNat i).length
  have henc : (encodeNat i).length = i + 1 :=
    CanonicalSATWitness.encodeNat_length i
  have hi : i ≤ N + 1 := by
    dsimp [N]
    rw [henc]
    omega
  have hN : 1 ≤ N + 1 := by omega
  have hisq :
      i ^ 2 ≤ (N + 1) ^ 2 := by
    simp only [Nat.pow_two]
    exact Nat.mul_le_mul hi hi
  have hlinquad :
      N + 1 ≤ (N + 1) ^ 2 := by
    simp only [Nat.pow_two]
    calc
      N + 1 = (N + 1) * 1 := by simp
      _ ≤ (N + 1) * (N + 1) :=
        Nat.mul_le_mul_left (N + 1) hN
  have hsqcube :
      (N + 1) ^ 2 ≤ (N + 1) ^ 3 := by
    calc
      (N + 1) ^ 2 = 1 * (N + 1) ^ 2 := by simp
      _ ≤ (N + 1) * (N + 1) ^ 2 :=
        Nat.mul_le_mul_right ((N + 1) ^ 2) hN
      _ = (N + 1) ^ 3 := by
        simp [Nat.pow_succ, Nat.mul_comm]
  have h2 :
      2 * i ^ 2 ≤ 2 * (N + 1) ^ 2 :=
    Nat.mul_le_mul_left 2 hisq
  have h12 :
      12 * i ≤ 12 * (N + 1) :=
    Nat.mul_le_mul_left 12 hi
  have hsq : 1 ≤ (N + 1) ^ 2 := by
    simp [Nat.pow_two]
    exact Nat.mul_pos hN hN
  have h5 :
      5 ≤ 5 * (N + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left 5 hsq
  have hquad :
      nonzeroReaderFuel i ≤ 19 * (N + 1) ^ 2 := by
    unfold nonzeroReaderFuel
    have h12q :
        12 * (N + 1) ≤ 12 * (N + 1) ^ 2 :=
      Nat.mul_le_mul_left 12 hlinquad
    omega
  have hquad64 :
      19 * (N + 1) ^ 2 ≤ 64 * (N + 1) ^ 2 :=
    Nat.mul_le_mul_right ((N + 1) ^ 2) (by omega)
  have hcubic :
      64 * (N + 1) ^ 2 ≤ 64 * (N + 1) ^ 3 :=
    Nat.mul_le_mul_left 64 hsqcube
  dsimp [preservingUnaryReaderTimeBound]
  exact Nat.le_trans hquad (Nat.le_trans hquad64 hcubic)

theorem zeroFuel_le_timeBound
    (witness : BitString) :
    5 ≤ preservingUnaryReaderTimeBound
      (witness.length + (encodeNat 0).length) := by
  unfold preservingUnaryReaderTimeBound
  have h : 1 ≤ witness.length + (encodeNat 0).length + 1 := by omega
  have hp : 1 ≤ (witness.length + (encodeNat 0).length + 1) ^ 3 := by
    have h2 :
        1 ≤ (witness.length + (encodeNat 0).length + 1) ^ 2 := by
      simp [Nat.pow_two]
      exact Nat.mul_pos h h
    calc
      1 ≤ (witness.length + (encodeNat 0).length + 1) ^ 2 := h2
      _ ≤ (witness.length + (encodeNat 0).length + 1) ^ 3 := by
        calc
          (witness.length + (encodeNat 0).length + 1) ^ 2 =
              1 * (witness.length + (encodeNat 0).length + 1) ^ 2 := by simp
          _ ≤ (witness.length + (encodeNat 0).length + 1) *
                (witness.length + (encodeNat 0).length + 1) ^ 2 :=
              Nat.mul_le_mul_right
                ((witness.length + (encodeNat 0).length + 1) ^ 2) h
          _ = (witness.length + (encodeNat 0).length + 1) ^ 3 := by
              simp [Nat.pow_succ, Nat.mul_comm]
  have hmul : 5 ≤ 64 * 1 := by omega
  calc
    5 ≤ 64 * 1 := hmul
    _ ≤ 64 * (witness.length + (encodeNat 0).length + 1) ^ 3 :=
      Nat.mul_le_mul_left 64 hp

#print axioms MCore.Real.P01PreservingUnaryReaderBound.preservingUnaryReaderTimeBound_poly
#print axioms MCore.Real.P01PreservingUnaryReaderBound.nonzeroReaderFuel_le_timeBound

end P01PreservingUnaryReaderBound
end Real
end MCore
