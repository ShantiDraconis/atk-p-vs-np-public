import MCore
namespace MCore.Material
structure PNPClosure (Instance Witness Machine : Type) where
  machine : Machine
  accepts : Instance → Witness → Prop
  polyHalts : Prop
  exactSemantics : Prop
  lowerBound : Prop
  polyHalts_proof : polyHalts
  exactSemantics_proof : exactSemantics
  lowerBound_proof : lowerBound

def MaterialPNPProducer (Instance Witness Machine : Type) : Prop :=
  Nonempty (PNPClosure Instance Witness Machine)
end MCore.Material
