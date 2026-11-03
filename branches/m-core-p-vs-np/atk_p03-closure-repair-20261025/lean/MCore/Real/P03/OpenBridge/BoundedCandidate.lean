import MCore.Real.P03UniformRangeDecoder

namespace MCore.Real.P03.OpenBridge.BoundedCandidate

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P03UniformRangeDecoder

abbrev Candidate :=
  BoundedSourceCandidate

def genuine
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    Candidate M (P02TableauDynamics.R_M M hTotal x) :=
  genuineSourceCandidate M hTotal x

#print axioms MCore.Real.P03.OpenBridge.BoundedCandidate.genuine

end MCore.Real.P03.OpenBridge.BoundedCandidate
