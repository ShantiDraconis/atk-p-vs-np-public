import MCore.Real.P01ExactVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawRecursiveBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01CheckedEvalRunBoundedCertificate
open P01ExactVerifierGlobalBudget

/-- One cubic work block.  This is exactly the already-certified canonical
verifier envelope. -/
abbrev rawChunk (n : Nat) : Nat :=
  checkedVerifierExactTimeBound n

/-- Decoder-recursion budget: one canonical cubic block per remaining decoder
fuel level. -/
def rawFailureBudget (fuel n : Nat) : Nat :=
  fuel * rawChunk n

/-- Final raw totalization bound.  Quartic is intentionally loose: P01 only
requires a polynomial bound, and the extra degree makes recursive malformed
input accounting transparent. -/
def checkedVerifierRawTimeBound : TimeBound :=
  fun n => 16384 * (n + 1) ^ 4

theorem checkedVerifierRawTimeBound_poly :
    PolynomialTimeBound checkedVerifierRawTimeBound := by
  exact ⟨16384, 4, fun n => Nat.le_refl _⟩

theorem square_le_cube (n : Nat) :
    (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
  rw [show (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) by
    simp [Nat.pow_succ]]
  exact Nat.le_mul_of_pos_right ((n + 1) ^ 2) (by omega)

theorem stepEnvelope_le_rawChunk (n : Nat) :
    checkedStepEnvelope n ≤ rawChunk n := by
  have hp := square_le_cube n
  have h1 :
      128 * (n + 1) ^ 2 ≤ 128 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_left 128 hp
  have h2 :
      128 * (n + 1) ^ 3 ≤ 8192 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)
  simpa [rawChunk, checkedStepEnvelope,
    checkedVerifierExactTimeBound] using Nat.le_trans h1 h2

theorem loopEnvelope_le_rawChunk (n : Nat) :
    checkedLoopStepEnvelope n ≤ rawChunk n := by
  have hp := square_le_cube n
  have h1 :
      256 * (n + 1) ^ 2 ≤ 256 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_left 256 hp
  have h2 :
      256 * (n + 1) ^ 3 ≤ 8192 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)
  simpa [rawChunk, checkedLoopStepEnvelope,
    checkedVerifierExactTimeBound] using Nat.le_trans h1 h2

/-- A full canonical child plus two local continuation envelopes fits one raw
cubic block. -/
theorem step_plus_linear_le_rawChunk (n : Nat) :
    checkedStepEnvelope n + (n + 1) ≤ rawChunk n := by
  have hs := stepEnvelope_le_rawChunk n
  have hp := square_le_cube n
  have hstep :
      checkedStepEnvelope n ≤ 128 * (n + 1) ^ 3 := by
    unfold checkedStepEnvelope
    exact Nat.mul_le_mul_left 128 hp
  have hlin : n + 1 ≤ (n + 1) ^ 3 := by
    calc
      n + 1 ≤ (n + 1) * (n + 1) :=
        Nat.le_mul_of_pos_right (n + 1) (by omega)
      _ ≤ ((n + 1) * (n + 1)) * (n + 1) :=
        Nat.mul_le_mul_right (n + 1)
          (Nat.le_mul_of_pos_right (n + 1) (by omega))
      _ = (n + 1) ^ 3 := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hsum :
      checkedStepEnvelope n + (n + 1) ≤
        129 * (n + 1) ^ 3 := by
    have := Nat.add_le_add hstep hlin
    omega
  have hcoef :
      129 * (n + 1) ^ 3 ≤ 8192 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)
  simpa [rawChunk, checkedVerifierExactTimeBound] using
    Nat.le_trans hsum hcoef

theorem circuit_plus_two_loops_le_rawChunk
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤ rawChunk n := by
  have hc := checkedCircuitBudget_le_exact_global n phi henc
  have hp := square_le_cube n
  have hl :
      checkedLoopStepEnvelope n ≤ 256 * (n + 1) ^ 3 := by
    unfold checkedLoopStepEnvelope
    exact Nat.mul_le_mul_left 256 hp
  unfold rawChunk checkedVerifierExactTimeBound
  omega

theorem circuit_plus_loop_le_rawChunk
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n ≤ rawChunk n := by
  have h :=
    circuit_plus_two_loops_le_rawChunk n phi henc
  omega

theorem rawFailureBudget_succ
    (fuel n : Nat) :
    rawFailureBudget (fuel + 1) n =
      rawFailureBudget fuel n + rawChunk n := by
  unfold rawFailureBudget
  simp [Nat.add_mul, Nat.one_mul]

theorem rawChunk_le_failureBudget
    (fuel n : Nat)
    (hfuel : 0 < fuel) :
    rawChunk n ≤ rawFailureBudget fuel n := by
  unfold rawFailureBudget
  have h : 1 ≤ fuel := hfuel
  simpa using Nat.mul_le_mul_right (rawChunk n) h

/-- Canonical cubic execution can always be reused under the final raw quartic
bound. -/
theorem exactTimeBound_le_rawTimeBound (n : Nat) :
    checkedVerifierExactTimeBound n ≤ checkedVerifierRawTimeBound n := by
  let X := 8192 * (n + 1) ^ 3
  have hfac : 1 ≤ 2 * (n + 1) := by omega
  have hmul : X ≤ (2 * (n + 1)) * X := by
    simpa using Nat.mul_le_mul_right X hfac
  dsimp [X] at hmul
  unfold checkedVerifierExactTimeBound checkedVerifierRawTimeBound
  calc
    8192 * (n + 1) ^ 3
        ≤ (2 * (n + 1)) * (8192 * (n + 1) ^ 3) := hmul
    _ = 16384 * (n + 1) ^ 4 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Root recursive malformed evaluation plus one scanner-sized cubic block fits
the quartic final bound. -/
theorem rootFailure_plus_chunk_le_rawTimeBound (n : Nat) :
    rawFailureBudget (n + 1) n + rawChunk n ≤
      checkedVerifierRawTimeBound n := by
  let X := rawChunk n
  have hfac : n + 2 ≤ 2 * (n + 1) := by omega
  have hmul :
      (n + 2) * X ≤ (2 * (n + 1)) * X :=
    Nat.mul_le_mul_right X hfac
  have hleft :
      rawFailureBudget (n + 1) n + rawChunk n =
        (n + 2) * X := by
    unfold rawFailureBudget
    rw [show n + 2 = (n + 1) + 1 by omega]
    dsimp [X]
    simp only [Nat.add_mul, Nat.one_mul]
  rw [hleft]
  calc
    (n + 2) * X ≤ (2 * (n + 1)) * X := hmul
    _ = checkedVerifierRawTimeBound n := by
      dsimp [X, rawChunk]
      unfold checkedVerifierExactTimeBound checkedVerifierRawTimeBound
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Any source scan overhead n+3 itself fits one cubic raw chunk. -/
theorem scanPlusOne_le_rawChunk (n : Nat) :
    n + 4 ≤ rawChunk n := by
  have h1 : n + 4 ≤ 4 * (n + 1) := by omega
  have h2 : 4 * (n + 1) ≤ 4 * (n + 1) ^ 3 := by
    have hp : n + 1 ≤ (n + 1) ^ 3 := by
      calc
        n + 1 ≤ (n + 1) * (n + 1) :=
          Nat.le_mul_of_pos_right (n + 1) (by omega)
        _ ≤ ((n + 1) * (n + 1)) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1)
            (Nat.le_mul_of_pos_right (n + 1) (by omega))
        _ = (n + 1) ^ 3 := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact Nat.mul_le_mul_left 4 hp
  have h3 :
      4 * (n + 1) ^ 3 ≤ 8192 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)
  simpa [rawChunk, checkedVerifierExactTimeBound] using
    Nat.le_trans h1 (Nat.le_trans h2 h3)

theorem scanLinear_le_rawChunk (n : Nat) :
    n + 3 ≤ rawChunk n := by
  have h1 : n + 3 ≤ 3 * (n + 1) := by omega
  have h2 : 3 * (n + 1) ≤ 3 * (n + 1) ^ 3 := by
    have hp : n + 1 ≤ (n + 1) ^ 3 := by
      calc
        n + 1 ≤ (n + 1) * (n + 1) :=
          Nat.le_mul_of_pos_right (n + 1) (by omega)
        _ ≤ ((n + 1) * (n + 1)) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1)
            (Nat.le_mul_of_pos_right (n + 1) (by omega))
        _ = (n + 1) ^ 3 := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact Nat.mul_le_mul_left 3 hp
  have h3 :
      3 * (n + 1) ^ 3 ≤ 8192 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)
  simpa [rawChunk, checkedVerifierExactTimeBound] using
    Nat.le_trans h1 (Nat.le_trans h2 h3)

#print axioms MCore.Real.P01RawRecursiveBudget.checkedVerifierRawTimeBound_poly
#print axioms MCore.Real.P01RawRecursiveBudget.circuit_plus_two_loops_le_rawChunk
#print axioms MCore.Real.P01RawRecursiveBudget.rootFailure_plus_chunk_le_rawTimeBound

end P01RawRecursiveBudget
end Real
end MCore
