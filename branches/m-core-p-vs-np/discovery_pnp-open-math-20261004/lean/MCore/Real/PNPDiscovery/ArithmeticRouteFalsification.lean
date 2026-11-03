import MCore.Real.PNPDiscovery.StrictOrbitLengthGrowth
import MCore.Real.PNPDiscovery.BarrierArithmeticFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Fail-closed route classification: equal-length arithmetic breaking is
incompatible with strict length growth whenever TerminalParityBarrier holds. -/
theorem arithmeticBreaker_incompatible_with_barrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal) :
    ¬ ArithmeticBarrierBreaker M hTotal := by
  intro B
  rcases B Hbar with ⟨seed, i, d, hLen, hBreak⟩
  exact (no_positive_odd_length_recurrence
    M hTotal seed i d) hLen

/-- Therefore the equal-length branch of BarrierArithmeticEscapeLaw is
unreachable on every positive odd pair.  The barrier always escapes through
length mismatch. -/
theorem barrierArithmeticEscape_degenerates_to_length
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length := by
  dsimp
  exact no_positive_odd_length_recurrence
    M hTotal seed i d

/-- Current route verdict. -/
inductive ArithmeticBreakerRouteStatus
  | closedByFalsification
  deriving Repr, DecidableEq

def arithmeticBreakerRouteStatus :
    ArithmeticBreakerRouteStatus :=
  .closedByFalsification

#print axioms MCore.Real.PNPDiscovery.arithmeticBreaker_incompatible_with_barrier
#print axioms MCore.Real.PNPDiscovery.barrierArithmeticEscape_degenerates_to_length

end PNPDiscovery
end Real
end MCore
