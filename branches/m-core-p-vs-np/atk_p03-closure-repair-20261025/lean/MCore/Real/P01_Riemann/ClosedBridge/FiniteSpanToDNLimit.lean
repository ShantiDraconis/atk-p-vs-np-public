import MCore.Real.P01_Riemann.SourceBinding

namespace MCore.Real.P01_Riemann.ClosedBridge.FiniteSpanToDNLimit

open P01_Riemann.SourceBinding

def evidence : SourceEvidence :=
  { name := "FiniteSpanToDNLimit"
    kind := .closedBridge
    sourceRepo := canonicalRHRepo
    sourceRef := canonicalDirectProducerRef
    sourcePath := "GATE_LEDGER.json"
    theoremName := "finiteSpanApproximatesChi_iff_DNLimit_eq_zero"
    semanticScope := "Source-bound equivalence: FiniteSpanApproximatesChi for the concrete generator family iff DNLimit = 0."
    sourceVerified := true }

theorem evidence_is_source_verified :
    evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P01_Riemann.ClosedBridge.FiniteSpanToDNLimit.evidence_is_source_verified

end MCore.Real.P01_Riemann.ClosedBridge.FiniteSpanToDNLimit
