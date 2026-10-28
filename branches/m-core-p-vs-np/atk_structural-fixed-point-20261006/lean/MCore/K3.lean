import MCore.K2
namespace MCore
inductive AuditDisposition where
  | passCertified
  | openBridge
  | refutedRoute
  | reviewRequired
  deriving DecidableEq, Repr
structure PredictedGap where
  id : String
  disposition : AuditDisposition
  node : CertNode
def k3_gap_node : CertNode := { status := .openBridge, statement := k1_node.status = .openBridge }
def k3_gap : PredictedGap := { id := "K3_algebra_audit", disposition := .openBridge, node := k3_gap_node }
theorem k3_gap_status_openBridge : k3_gap_node.status = .openBridge := rfl
theorem k3_gap_not_proved : k3_gap_node.status ≠ .provedProperty := by decide
theorem k3_gap_not_certified : ¬ Nonempty (ProofCertificate k3_gap_node) := by intro h; rcases h with ⟨c⟩; exact k3_gap_not_proved c.status_proved
end MCore
