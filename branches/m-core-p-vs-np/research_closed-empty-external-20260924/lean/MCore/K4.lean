import MCore.K3
namespace MCore
def k4_open_node : CertNode := k3_gap_node
theorem k4_status_openBridge : k4_open_node.status = .openBridge := k3_gap_status_openBridge
theorem k4_no_promotion : ¬ Nonempty (ProofCertificate k4_open_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k3_gap_not_proved c.status_proved
end MCore
