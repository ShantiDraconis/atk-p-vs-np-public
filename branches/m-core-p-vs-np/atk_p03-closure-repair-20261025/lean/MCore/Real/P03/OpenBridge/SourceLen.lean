import MCore.Real.P03UniformRangeDecoder

namespace MCore.Real.P03.OpenBridge.SourceLen

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TableauDynamics
open P03UniformRangeDecoder

theorem source_len_bound
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    x.length ≤ (R_M M hTotal x).length :=
  source_length_le_reduction_length M hTotal x

#print axioms MCore.Real.P03.OpenBridge.SourceLen.source_len_bound

end MCore.Real.P03.OpenBridge.SourceLen
