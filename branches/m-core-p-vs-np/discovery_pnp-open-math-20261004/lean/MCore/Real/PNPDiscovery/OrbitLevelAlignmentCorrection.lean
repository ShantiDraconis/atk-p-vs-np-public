import MCore.Real.PNPDiscovery.SourceCellBitTransportClosed
import MCore.Real.PNPDiscovery.ReadCone
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics

/-- Correct cone for a mismatch produced by encoding x and y: the mismatch
lives in R_M(x) versus R_M(y), so visibility must be measured at those
successor inputs, not at x and y themselves. -/
def SuccessorSharedReadConePrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString) : Nat :=
  SharedReadConePrefix M
    (R_M M hTotal x)
    (R_M M hTotal y)

/-- Pure arithmetic visibility split at the correctly aligned successor cone. -/
theorem sourceBit_beforeSuccessorCone_or_after
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (q : Nat) :
    q < SuccessorSharedReadConePrefix M hTotal x y ∨
      SuccessorSharedReadConePrefix M hTotal x y ≤ q := by
  omega

/-- If all differences between the two successor encodings are hidden beyond
their shared cone, the candidate reaches the same terminal state on R(x),R(y). -/
def SuccessorDifferencesHidden
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString) : Prop :=
  (R_M M hTotal x).take
      (SuccessorSharedReadConePrefix M hTotal x y) =
    (R_M M hTotal y).take
      (SuccessorSharedReadConePrefix M hTotal x y)

theorem successorDifferencesHidden_closes_terminalState
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (H : SuccessorDifferencesHidden M hTotal x y) :
    terminalState M (R_M M hTotal x) =
      terminalState M (R_M M hTotal y) := by
  exact sharedReadCone_invisibility
    M hTotal
    (R_M M hTotal x)
    (R_M M hTotal y)
    H

/-- Correctly aligned hidden-source growth expression. -/
def SuccessorHiddenSourceGrowth
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (q : Nat) : Prop :=
  SuccessorSharedReadConePrefix M hTotal x y ≤ q

theorem successorHiddenSourceGrowth_unfold
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (q : Nat)
    (H : SuccessorHiddenSourceGrowth M hTotal x y q) :
    Nat.min
      (M.timeBound (R_M M hTotal x).length)
      (M.timeBound (R_M M hTotal y).length) + 1 ≤ q := by
  exact H

#print axioms MCore.Real.PNPDiscovery.sourceBit_beforeSuccessorCone_or_after
#print axioms MCore.Real.PNPDiscovery.successorDifferencesHidden_closes_terminalState
#print axioms MCore.Real.PNPDiscovery.successorHiddenSourceGrowth_unfold

end PNPDiscovery
end Real
end MCore
