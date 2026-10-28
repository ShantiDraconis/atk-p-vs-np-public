import MCore.K4
namespace MCore
structure OpenBridgeFirewall (n : CertNode) : Prop where
  open_status : n.status = .openBridge
  certificate_blocked : ¬ Nonempty (ProofCertificate n)
def k5_firewall : OpenBridgeFirewall k4_open_node := { open_status := k4_status_openBridge, certificate_blocked := k4_no_promotion }
theorem k5_openBridge_cannot_certify : ¬ Nonempty (ProofCertificate k4_open_node) := k5_firewall.certificate_blocked
end MCore
