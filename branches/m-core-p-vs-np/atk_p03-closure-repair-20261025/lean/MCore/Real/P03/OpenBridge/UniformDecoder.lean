import MCore.Real.P03UniformRangeDecoder

namespace MCore.Real.P03.OpenBridge.UniformDecoder

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P03UniformRangeDecoder

/-- CLOSED pointwise source recovery. -/
theorem pointwise_closed
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ n t,
      SourceRecovery.decodeSourceBits
        (P02ComplementRunRealization.complementToNTMCandidate M)
        n t
        (P02TableauDynamics.R_M M hTotal x) = some x :=
  pointwise_source_recovery M hTotal x

/-- OPEN uniform decoder target. Target alias only. -/
abbrev UniformOpenTarget
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :=
  UniformRangeDecoder M hTotal

abbrev ExistsUniformDecoder : Prop :=
  UniformRangeDecoderLaw

#print axioms MCore.Real.P03.OpenBridge.UniformDecoder.pointwise_closed

end MCore.Real.P03.OpenBridge.UniformDecoder
