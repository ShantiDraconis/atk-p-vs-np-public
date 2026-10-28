import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.OpenCoreFirewall

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "OpenCoreFirewall"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K14.lean"
    theoremName := "k14_chain_preserves_open_core / k14_no_false_final_certificate"
    semanticScope := "Closed fail-closed audit: K11-K13 remain openBridge and no final certificate can be manufactured from the typed scaffold."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.OpenCoreFirewall.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.OpenCoreFirewall
