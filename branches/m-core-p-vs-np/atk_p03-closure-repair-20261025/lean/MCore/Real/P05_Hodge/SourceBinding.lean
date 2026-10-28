namespace MCore.Real.P05_Hodge.SourceBinding

inductive EvidenceKind where
  | closedBase
  | closedBridge
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

def canonicalHodgeRepo : String := "ShantiDraconis/m-core-hodge"
def canonicalFrozenRef : String := "42eaf7d4d639871f82eceb121ee525a6c4f30d84"
def canonicalMainRef : String := "a994aebb57a3032f3c6c99d785b19aa650392630"

end MCore.Real.P05_Hodge.SourceBinding
