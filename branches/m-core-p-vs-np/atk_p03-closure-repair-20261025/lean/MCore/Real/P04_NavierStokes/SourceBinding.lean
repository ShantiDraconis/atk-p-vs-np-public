namespace MCore.Real.P04_NavierStokes.SourceBinding

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

def canonicalNSRepo : String := "ShantiDraconis/navier-stokes-critical-barrier-audit"
def canonicalNSRef : String := "df808543535d34d4e8c46096b3455d76b0151fa2"

end MCore.Real.P04_NavierStokes.SourceBinding
