import MCore.Real.P01PreservingUnaryReaderMaterial

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderBound

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryPhysicalRuns
open P01PreservingUnaryReaderMaterial

/-- Compatibility name for the exact material reader fuel. -/
def nonzeroReaderFuel (i : Nat) : Nat :=
  preservingUnaryExactFuel i

/-- Compatibility name for the already-certified quadratic reader bound. -/
def preservingUnaryReaderTimeBound : TimeBound :=
  preservingUnaryTimeBound

theorem preservingUnaryReaderTimeBound_poly :
    PolynomialTimeBound preservingUnaryReaderTimeBound := by
  simpa [preservingUnaryReaderTimeBound] using preservingUnaryTimeBound_poly

theorem nonzeroReaderFuel_le_timeBound
    (witness : BitString) (i : Nat) :
    nonzeroReaderFuel i ≤
      preservingUnaryReaderTimeBound
        (witness.length + (encodeNat i).length) := by
  have hq := preservingUnaryExactFuel_le_quadratic i
  have henc := encodeNat_length i
  have hil :
      i + 1 ≤ witness.length + (encodeNat i).length + 1 := by
    rw [henc]
    omega
  have hsq :
      (i + 1) ^ 2 ≤
        (witness.length + (encodeNat i).length + 1) ^ 2 :=
    Nat.pow_le_pow_left hil 2
  unfold nonzeroReaderFuel preservingUnaryReaderTimeBound preservingUnaryTimeBound
  exact Nat.le_trans hq (Nat.mul_le_mul_left 16 hsq)

theorem zeroFuel_le_timeBound
    (witness : BitString) :
    5 ≤ preservingUnaryReaderTimeBound
      (witness.length + (encodeNat 0).length) := by
  unfold preservingUnaryReaderTimeBound preservingUnaryTimeBound
  have hpos :
      1 ≤ witness.length + (encodeNat 0).length + 1 := by omega
  have hsq :
      1 ≤ (witness.length + (encodeNat 0).length + 1) ^ 2 := by
    simpa [Nat.pow_two] using
      Nat.mul_le_mul hpos hpos
  have h16 :
      16 ≤ 16 * (witness.length + (encodeNat 0).length + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left 16 hsq
  omega

#print axioms MCore.Real.P01PreservingUnaryReaderBound.preservingUnaryReaderTimeBound_poly
#print axioms MCore.Real.P01PreservingUnaryReaderBound.nonzeroReaderFuel_le_timeBound
#print axioms MCore.Real.P01PreservingUnaryReaderBound.zeroFuel_le_timeBound

end P01PreservingUnaryReaderBound
end Real
end MCore
