namespace MCore.Real.P02_YangMills.SourceBinding

inductive EvidenceKind where
  | closedBase
  | closedBridge
  deriving Repr, DecidableEq, BEq

structure SourceClosedEvidence where
  name : String
  kind : EvidenceKind
  sourceRepo : String
  sourceRef : String
  sourcePath : String
  theoremName : String
  semanticScope : String
  sourceVerified : Bool
  deriving Repr, DecidableEq

def canonicalYMRepo : String := "ShantiDraconis/m-core-yang-mills"
def canonicalYMRef : String := "cd4bbfd348b607bd24ed0c6d605207b764286f58"

end MCore.Real.P02_YangMills.SourceBinding
