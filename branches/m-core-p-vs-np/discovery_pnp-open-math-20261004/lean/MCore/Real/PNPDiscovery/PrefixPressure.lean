import MCore.Real.PNPDiscovery.ReadConeFrontier
import MCore.Real.P03PerfectFlipConstruction

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P03PerfectFlipConstruction

/-- Every positive-index discovery-orbit point is a genuine reduction image,
hence begins with the fixed canonical AND tag 100. -/
theorem orbit_succ_fixed_prefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    ∃ tail : BitString,
      orbit M hTotal seed (n + 1) =
        [true, false, false] ++ tail := by
  have h :=
    R_M_fixed_prefix
      M hTotal (orbit M hTotal seed n)
  simpa [orbit, reductionMap_eq_R_M] using h

/-- Any two positive-index orbit points agree on their first three bits. -/
theorem positive_orbit_take_three
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i j : Nat) :
    (orbit M hTotal seed (i + 1)).take 3 =
      (orbit M hTotal seed (j + 1)).take 3 := by
  rcases orbit_succ_fixed_prefix M hTotal seed i with ⟨ti, hi⟩
  rcases orbit_succ_fixed_prefix M hTotal seed j with ⟨tj, hj⟩
  simp [hi, hj]

/-- Therefore a terminal parity barrier forces the shared observable cone of
any odd-separated positive orbit pair to extend beyond the three fixed bits.
This is the first arithmetic constraint emitted by the negative regime. -/
theorem parityBarrier_forces_sharedCone_gt_three
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    3 <
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  by_contra hNot
  have hle :
      SharedReadConePrefix M
          (orbit M hTotal seed (i + 1))
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))) ≤ 3 := by
    omega
  have h3 :=
    positive_orbit_take_three
      M hTotal seed
      i
      (i + (2 * d + 1))
  have hCone :
      (orbit M hTotal seed (i + 1)).take
          (SharedReadConePrefix M
            (orbit M hTotal seed (i + 1))
            (orbit M hTotal seed ((i + 1) + (2 * d + 1)))) =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).take
          (SharedReadConePrefix M
            (orbit M hTotal seed (i + 1))
            (orbit M hTotal seed ((i + 1) + (2 * d + 1)))) := by
    have := congrArg
      (fun xs : BitString =>
        xs.take
          (SharedReadConePrefix M
            (orbit M hTotal seed (i + 1))
            (orbit M hTotal seed ((i + 1) + (2 * d + 1)))))
      h3
    simpa [List.take_take, Nat.min_eq_left hle] using this
  have hDiff :=
    parityBarrier_forces_sharedCone_difference
      M hTotal H seed (i + 1) d
  exact hDiff hCone

/-- Unfolding the shared cone gives a concrete clock constraint. -/
theorem parityBarrier_forces_min_clock_ge_three
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    3 ≤
      Nat.min
        (M.timeBound (orbit M hTotal seed (i + 1)).length)
        (M.timeBound
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) := by
  have h :=
    parityBarrier_forces_sharedCone_gt_three
      M hTotal H seed i d
  unfold SharedReadConePrefix at h
  omega

#print axioms MCore.Real.PNPDiscovery.orbit_succ_fixed_prefix
#print axioms MCore.Real.PNPDiscovery.positive_orbit_take_three
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_sharedCone_gt_three
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_min_clock_ge_three

end PNPDiscovery
end Real
end MCore
