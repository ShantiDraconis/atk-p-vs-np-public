namespace MCore.Real.P03.ClosedBase.SourceBinding
structure ClosedSourceEvidence where
  name : String
  sourceRepo : String
  sourceRef : String
  theoremName : String
  semanticScope : String
  sourceVerified : Bool
  deriving Repr, DecidableEq
def canonicalRepo : String := "ShantiDraconis/m-core-p-vs-np"
end MCore.Real.P03.ClosedBase.SourceBinding
