import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.OpenBridge.ConcreteAlgebraicityPayloadTarget

open P05_Hodge.SourceBinding

def targetName : String := "ConcreteAlgebraicityPayload"
def equivalentRegressionTarget : String := "TrivialQbarR2Payload"
def sourceRepo : String := canonicalHodgeRepo
def sourceRef : String := canonicalFrozenRef
def sourcePath : String := "GATE_LEDGER.json"
def sourceTheorem : String := "trivial_qbar_r2_payload_iff_concrete_payload"

theorem source_ref_fixed :
    sourceRef = "42eaf7d4d639871f82eceb121ee525a6c4f30d84" := rfl

#print axioms MCore.Real.P05_Hodge.OpenBridge.ConcreteAlgebraicityPayloadTarget.source_ref_fixed

end MCore.Real.P05_Hodge.OpenBridge.ConcreteAlgebraicityPayloadTarget
