import MCore.Real.P02TerminalForcingG2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02ClockBridgeMaterial

open CanonicalFinalProof
open MachineRunLemmas

def polynomialMajorant (c e : Nat) : TimeBound :=
  fun n => c * (n + 1) ^ e

theorem polynomialMajorant_poly (c e : Nat) :
    PolynomialTimeBound (polynomialMajorant c e) := by
  refine ⟨c, e, ?_⟩
  intro n
  exact Nat.le_refl _

def withMajorantClock
    (M : PolyDTMCandidate)
    (c e : Nat) :
    PolyDTMCandidate :=
  { M with
    timeBound := polynomialMajorant c e
    time_poly := polynomialMajorant_poly c e }

theorem correctAt_mono_clock
    (M : PolyDTMCandidate)
    (c e : Nat)
    (hLe : ∀ n, M.timeBound n ≤ polynomialMajorant c e n)
    (L : BitLanguage)
    (x : BitString)
    (hCorrect : M.CorrectAt L x) :
    (withMajorantClock M c e).CorrectAt L x := by
  unfold PolyDTMCandidate.CorrectAt at hCorrect ⊢
  rcases hCorrect with ⟨hHalt, hDecide⟩
  constructor
  · exact haltsWithin_mono
      M.machine
      (initialTMConfig M.machine x)
      (hLe x.length)
      hHalt
  · have hRun :
        M.machine.run (polynomialMajorant c e x.length)
            (initialTMConfig M.machine x) =
          M.machine.run (M.timeBound x.length)
            (initialTMConfig M.machine x) := by
      exact run_to_larger_fuel_of_halt
        M.machine
        (initialTMConfig M.machine x)
        (M.machine.run (M.timeBound x.length)
          (initialTMConfig M.machine x))
        (hLe x.length)
        rfl
        hHalt
    simpa [withMajorantClock, hRun] using hDecide

theorem exists_majorant_candidate_preserving_correctAt
    (M : PolyDTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (hCorrect : M.CorrectAt L x) :
    ∃ c e : Nat,
      (withMajorantClock M c e).CorrectAt L x := by
  rcases M.time_poly with ⟨c, e, hLe⟩
  exact ⟨c, e, correctAt_mono_clock M c e hLe L x hCorrect⟩

#print axioms MCore.Real.P02ClockBridgeMaterial.polynomialMajorant_poly
#print axioms MCore.Real.P02ClockBridgeMaterial.correctAt_mono_clock
#print axioms MCore.Real.P02ClockBridgeMaterial.exists_majorant_candidate_preserving_correctAt

end P02ClockBridgeMaterial
end Real
end MCore
