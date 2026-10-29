import MCore.K1

namespace MCore

structure CertNode where
  status : SignatureStatus
  statement : Prop

structure ProofCertificate (n : CertNode) where
  status_proved : n.status = .provedProperty
  proof : n.statement

def k1_node : CertNode :=
  { status := k1Target.status
    statement := k1Target.status = .openBridge }

theorem k2_node_status_openBridge : k1_node.status = .openBridge := by
  exact k1_status_openBridge

theorem k2_node_not_proved : k1_node.status ≠ .provedProperty := by
  simpa [k1_node] using k1_not_proved

theorem bridge_not_certified : ¬ Nonempty (ProofCertificate k1_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k2_node_not_proved c.status_proved

end MCore
