import MCore.Real.PNPDiscovery.SourcePrefixCoverageClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Closed source-prefix pressure: no open bridge argument remains. -/
theorem closed_sourcePrefix_pressures_barrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (A :
      SourcePrefixLayoutAlignment M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
        k) :
    sourcePrefixBitEnd
        (complementToNTMCandidate M)
        (orbit M hTotal seed (i + 1))
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        k <
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  exact sourcePrefixCoverage_pressures_barrier
    sourcePrefixCoverage_closed
    M hTotal Hbar seed i d k A

/-- Equivalent clock inequality after unfolding SharedReadConePrefix. -/
theorem closed_sourcePrefix_le_minClock
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (A :
      SourcePrefixLayoutAlignment M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
        k) :
    sourcePrefixBitEnd
        (complementToNTMCandidate M)
        (orbit M hTotal seed (i + 1))
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        k ≤
      Nat.min
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        (M.timeBound
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) := by
  have h :=
    closed_sourcePrefix_pressures_barrier
      M hTotal Hbar seed i d k A
  unfold SharedReadConePrefix at h
  omega

/-- One-step growth pressure: if k+1 source cells align, the barrier must pay
for the larger k+1 encoded prefix as well. -/
theorem barrier_pays_each_aligned_source_cell
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (A :
      SourcePrefixLayoutAlignment M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
        (k + 1)) :
    sourcePrefixBitEnd
        (complementToNTMCandidate M)
        (orbit M hTotal seed (i + 1))
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        (k + 1) ≤
      Nat.min
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        (M.timeBound
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :=
  closed_sourcePrefix_le_minClock
    M hTotal Hbar seed i d (k + 1) A

#print axioms MCore.Real.PNPDiscovery.closed_sourcePrefix_pressures_barrier
#print axioms MCore.Real.PNPDiscovery.closed_sourcePrefix_le_minClock
#print axioms MCore.Real.PNPDiscovery.barrier_pays_each_aligned_source_cell

end PNPDiscovery
end Real
end MCore
