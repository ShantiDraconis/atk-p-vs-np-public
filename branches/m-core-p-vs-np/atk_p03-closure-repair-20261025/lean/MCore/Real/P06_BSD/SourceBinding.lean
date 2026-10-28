namespace MCore.Real.P06_BSD.SourceBinding

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

def canonicalBSDRepo : String := "ShantiDraconis/m-core-bsd"
def canonicalMainRef : String := "ed28a02170001a4afb0b3230e1bda238dcb5fa9f"
def canonicalFirewallRef : String := "c1e7b245726c4c65f5f9f878acefb86460746f4a"

end MCore.Real.P06_BSD.SourceBinding
