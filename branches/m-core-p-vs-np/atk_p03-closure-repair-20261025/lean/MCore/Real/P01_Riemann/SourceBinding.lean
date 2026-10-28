namespace MCore.Real.P01_Riemann.SourceBinding

inductive EvidenceKind where
  | closedBase
  | closedBridge
  | sourceMiddle
  | openBridge
  deriving Repr, DecidableEq, BEq

structure SourceEvidence where
  name : String
  kind : EvidenceKind
  sourceRepo : String
  sourceRef : String
  sourcePath : String
  theoremName : String
  semanticScope : String
  sourceVerified : Bool
  deriving Repr, DecidableEq

def canonicalRHRepo : String := "ShantiDraconis/m-core-riemann"
def canonicalMainRef : String := "b239b00cec143f0259eaeb92068dee63474ed177"
def canonicalFrozenBaseRef : String := "5c66f8dca03834f24a61a9b1219e7af9d4892dd6"
def canonicalDirectProducerRef : String := "d6a291b4563f9021f74ab63cc983d44f079472da"

end MCore.Real.P01_Riemann.SourceBinding
