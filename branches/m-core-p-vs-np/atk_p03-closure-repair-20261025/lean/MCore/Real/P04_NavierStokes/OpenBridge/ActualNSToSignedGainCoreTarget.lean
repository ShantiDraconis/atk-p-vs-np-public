import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.OpenBridge.ActualNSToSignedGainCoreTarget

open P04_NavierStokes.SourceBinding

def targetName : String :=
  "ActualNSToSignedGainCore State ActualNS nu data"

def sourceRepo : String := canonicalNSRepo
def sourceRef : String := canonicalNSRef
def sourcePath : String := "audit/producer-first/SignedGainCore.lean"
def sourceDefinition : String := "ActualNSToSignedGainCore"

theorem source_ref_fixed :
    sourceRef = "df808543535d34d4e8c46096b3455d76b0151fa2" := rfl

#print axioms MCore.Real.P04_NavierStokes.OpenBridge.ActualNSToSignedGainCoreTarget.source_ref_fixed

end MCore.Real.P04_NavierStokes.OpenBridge.ActualNSToSignedGainCoreTarget
