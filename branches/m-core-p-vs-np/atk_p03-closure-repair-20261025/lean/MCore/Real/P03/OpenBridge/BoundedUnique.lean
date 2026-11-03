import MCore.Real.P03UniformRangeDecoder

namespace MCore.Real.P03.OpenBridge.BoundedUnique

open P03UniformRangeDecoder

/-- OPEN SUBGAP. This is a target alias only, not a theorem or inhabitant. -/
abbrev OpenTarget
    (M : CanonicalFinalProof.PolyDTMCandidate)
    (hTotal : P02KleeneUniversalBridge.DeclaredClockTotal M) : Prop :=
  BoundedSourceUnique M hTotal

/-- Global constructive search target for the B-side. Still OPEN. -/
abbrev ExistsUniqueDecoderSource : Prop :=
  BoundedSourceUniquenessGap

end MCore.Real.P03.OpenBridge.BoundedUnique
