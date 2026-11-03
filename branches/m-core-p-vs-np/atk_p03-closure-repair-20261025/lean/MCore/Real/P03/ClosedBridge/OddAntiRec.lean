import MCore.Real.P03PerfectFlipDichotomy

namespace MCore.Real.P03.ClosedBridge.OddAntiRec

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TableauDynamics
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

theorem closed_perfectFlip_odd_anti_recurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hFlip : PerfectFlip M hTotal)
    (seed : BitString)
    (i d : Nat) :
    ¬ ObsEquiv M
        (Orbit (R_M M hTotal) seed i)
        (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) :=
  perfectFlip_odd_not_equiv hFlip seed i d

#print axioms MCore.Real.P03.ClosedBridge.OddAntiRec.closed_perfectFlip_odd_anti_recurrence

end MCore.Real.P03.ClosedBridge.OddAntiRec
