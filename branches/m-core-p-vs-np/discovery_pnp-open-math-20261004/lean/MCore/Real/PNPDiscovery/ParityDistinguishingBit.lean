import MCore.Real.PNPDiscovery.ClockVsEncodingLayout

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction
open P02TableauDynamics

/-- Concrete witness that two bitstrings are already distinguishable by their
prefix of length k. -/
structure DistinguishingPrefix
    (x y : BitString) where
  k : Nat
  differs : x.take k ≠ y.take k

/-- In the terminal-parity-barrier regime, every odd-separated positive pair
has a concrete distinguishing prefix contained in the shared read cone. -/
def parityBarrier_distinguishingPrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    DistinguishingPrefix
      (orbit M hTotal seed (i + 1))
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))) :=
  { k :=
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
    differs :=
      parityBarrier_forces_sharedCone_difference
        M hTotal H seed (i + 1) d }

/-- Every such distinguishing prefix lies at or below the read-cone boundary
by construction. -/
theorem parityBarrier_distinguishingPrefix_withinCone
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    (parityBarrier_distinguishingPrefix
      M hTotal H seed i d).k =
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  rfl

/-- Stable-prefix pressure excludes every k already proved stable: a barrier
witness must occur strictly after k. -/
theorem stablePrefix_before_distinguishingPrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (hk : StablePrefixAt M hTotal k) :
    k <
      (parityBarrier_distinguishingPrefix
        M hTotal H seed i d).k := by
  exact parityBarrier_beats_every_stablePrefix
    M hTotal H seed i d k hk

/-- In particular, the currently certified universal prefix 100 forces every
barrier witness beyond the first three bits. -/
theorem distinguishingPrefix_after_three
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    3 <
      (parityBarrier_distinguishingPrefix
        M hTotal H seed i d).k := by
  exact stablePrefix_before_distinguishingPrefix
    M hTotal H seed i d 3
    (stablePrefix_three M hTotal)

/-- A one-step extension failure is the exact local object to classify by
encoding region.  This definition deliberately contains no complexity
endpoint. -/
structure PrefixBreak
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  k : Nat
  stable_before : StablePrefixAt M hTotal k
  unstable_after : ¬ StablePrefixAt M hTotal (k + 1)

/-- Mechanical witness-extraction interface for a PrefixBreak.  This is
REDUCIBLE/CLOSED bookkeeping, not a new OPEN_MATH claim; the genuinely new
next step is to classify the differing bit by a literal encoding region. -/
def PrefixBreakWitnessExtraction : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ∀ B : PrefixBreak M hTotal,
      ∃ x y : BitString,
        (R_M M hTotal x).take B.k =
          (R_M M hTotal y).take B.k ∧
        (R_M M hTotal x).take (B.k + 1) ≠
          (R_M M hTotal y).take (B.k + 1)

theorem prefixBreakWitnessExtraction_closed :
    PrefixBreakWitnessExtraction := by
  intro M hTotal B
  exact firstUnstableExtension_has_pair
    M hTotal B.k
    ⟨B.stable_before, B.unstable_after⟩

#print axioms MCore.Real.PNPDiscovery.parityBarrier_distinguishingPrefix
#print axioms MCore.Real.PNPDiscovery.stablePrefix_before_distinguishingPrefix
#print axioms MCore.Real.PNPDiscovery.distinguishingPrefix_after_three
#print axioms MCore.Real.PNPDiscovery.prefixBreakWitnessExtraction_closed

end PNPDiscovery
end Real
end MCore
