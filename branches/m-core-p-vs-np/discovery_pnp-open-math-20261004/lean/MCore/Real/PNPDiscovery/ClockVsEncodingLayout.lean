import MCore.Real.PNPDiscovery.ReductionPrefixFormula
import MCore.Real.PNPDiscovery.ReadConeFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P02ExactDiagonalFrontier

/-- A stable reduction prefix that covers the complete shared read cone of one
odd-separated positive orbit pair.  This is strictly structural. -/
structure PrefixDominatesOddPair
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i : Nat
  d : Nat
  k : Nat
  stable : StablePrefixAt M hTotal k
  covers :
    SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) ≤ k

/-- Once a stable prefix covers the shared cone, the terminal-state recurrence
is forced with no additional complexity hypothesis. -/
theorem prefixDominatesOddPair_to_sharedCollision
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (W : PrefixDominatesOddPair M hTotal) :
    OddSharedReadConeCollision M hTotal := by
  refine ⟨W.seed, W.i + 1, W.d, ?_⟩
  let x := orbit M hTotal W.seed (W.i + 1)
  let y :=
    orbit M hTotal W.seed
      ((W.i + 1) + (2 * W.d + 1))
  have hStable :
      x.take W.k = y.take W.k := by
    change
      (R_M M hTotal (orbit M hTotal W.seed W.i)).take W.k =
        (R_M M hTotal
          (orbit M hTotal W.seed
            (W.i + (2 * W.d + 1)))).take W.k
    simpa [orbit, reductionMap_eq_R_M, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      W.stable
        (orbit M hTotal W.seed W.i)
        (orbit M hTotal W.seed (W.i + (2 * W.d + 1)))
  have hTake := congrArg
    (fun bs : BitString =>
      bs.take (SharedReadConePrefix M x y))
    hStable
  simpa [x, y, List.take_take, Nat.min_eq_left W.covers] using hTake

theorem prefixDominatesOddPair_to_exact
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : PrefixDominatesOddPair M hTotal) :
    ExactDiagonalWitness M := by
  have hTerminal :
      OddTerminalStateRecurrence M hTotal :=
    oddSharedReadConeCollision_to_terminal
      M hTotal (prefixDominatesOddPair_to_sharedCollision M hTotal W)
  rcases oddTerminalStateRecurrence_to_observable M hTotal hTerminal with
    ⟨seed, i, d, hObs⟩
  have hOddGeneric :
      P02OddSemanticRecurrence.OddSemanticRecurrence
        M (P02TableauDynamics.R_M M hTotal) := by
    refine ⟨seed, i, i + (2 * d + 1), ⟨d, rfl⟩, ?_⟩
    simpa [P02OddSemanticRecurrence.ObsEquiv,
      orbit_eq_genericOrbit M hTotal seed] using hObs
  rcases P02OddSemanticRecurrence.oddRecurrence_implies_adjacent hOddGeneric with
    ⟨z, hz⟩
  exact acceptance_collision_gives_exact_witness
    M hTotal z 0
    (by simpa [AcceptanceCollision, orbit, reductionMap_eq_R_M,
      P02OddSemanticRecurrence.ObsEquiv] using hz)

/-- Uniform sufficient producer obtained by covering a read cone with a
proved-stable encoding prefix. -/
def PrefixDominanceProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    Nonempty (PrefixDominatesOddPair M hTotal)

theorem prefixDominanceProducer_to_exact
    (B : PrefixDominanceProducer) :
    TotalExactDiagonalProducer := by
  intro M hTotal
  rcases B M hTotal with ⟨W⟩
  exact prefixDominatesOddPair_to_exact W

/-- Counter-regime pressure: if terminal recurrence is impossible, then no
proved stable prefix can ever cover the shared cone of an odd positive pair. -/
theorem parityBarrier_beats_every_stablePrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (hk : StablePrefixAt M hTotal k) :
    k <
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  by_contra hNot
  have hCover :
      SharedReadConePrefix M
          (orbit M hTotal seed (i + 1))
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))) ≤ k := by
    omega
  let W : PrefixDominatesOddPair M hTotal :=
    { seed := seed
      i := i
      d := d
      k := k
      stable := hk
      covers := hCover }
  have hRec :=
    oddSharedReadConeCollision_to_terminal
      M hTotal (prefixDominatesOddPair_to_sharedCollision M hTotal W)
  rcases hRec with ⟨s, j, e, hEq⟩
  exact H s j e hEq

/-- Clock form of the same pressure.  Every stable prefix length is a lower
bound on both declared clocks of every odd positive pair in the barrier
regime. -/
theorem parityBarrier_stablePrefix_le_minClock
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (hk : StablePrefixAt M hTotal k) :
    k ≤
      Nat.min
        (M.timeBound (orbit M hTotal seed (i + 1)).length)
        (M.timeBound
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) := by
  have h :=
    parityBarrier_beats_every_stablePrefix
      M hTotal H seed i d k hk
  unfold SharedReadConePrefix at h
  omega

#print axioms MCore.Real.PNPDiscovery.prefixDominatesOddPair_to_sharedCollision
#print axioms MCore.Real.PNPDiscovery.prefixDominanceProducer_to_exact
#print axioms MCore.Real.PNPDiscovery.parityBarrier_beats_every_stablePrefix
#print axioms MCore.Real.PNPDiscovery.parityBarrier_stablePrefix_le_minClock

end PNPDiscovery
end Real
end MCore
