import MCore.Real.OfficialModel

namespace MCore
namespace Real
namespace EncodingNormalization

open CanonicalFinalProof

/-- Explicit normalization between the hardened canonical bit representation
and the representation used by an external model.  Both directions carry
polynomial cost bounds and round-trip laws; there is no free arbitrary encoder. -/
structure EncodingNormalization where
  canonicalToExternal : BitString → BitString
  externalToCanonical : BitString → BitString
  left_inverse :
    ∀ bs : BitString,
      externalToCanonical (canonicalToExternal bs) = bs
  right_inverse :
    ∀ bs : BitString,
      canonicalToExternal (externalToCanonical bs) = bs
  encodeCost : TimeBound
  decodeCost : TimeBound
  encodeCost_poly : PolynomialTimeBound encodeCost
  decodeCost_poly : PolynomialTimeBound decodeCost
  encode_length_le_cost :
    ∀ bs : BitString,
      (canonicalToExternal bs).length ≤ encodeCost bs.length
  decode_length_le_cost :
    ∀ bs : BitString,
      (externalToCanonical bs).length ≤ decodeCost bs.length

theorem canonical_roundtrip_semantics
    (N : EncodingNormalization)
    (L : BitLanguage)
    (bs : BitString) :
    L (N.externalToCanonical (N.canonicalToExternal bs)) ↔ L bs := by
  rw [N.left_inverse]

theorem external_roundtrip_semantics
    (N : EncodingNormalization)
    (L : BitLanguage)
    (bs : BitString) :
    L (N.canonicalToExternal (N.externalToCanonical bs)) ↔ L bs := by
  rw [N.right_inverse]

end EncodingNormalization
end Real
end MCore
