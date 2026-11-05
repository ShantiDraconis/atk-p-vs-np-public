import MCore.K5
namespace MCore
structure Dependency where
  source : CertNode
  target : CertNode

def k6_dependency : Dependency := { source := k1_node, target := k4_open_node }
theorem k6_source_open : k6_dependency.source.status = .openBridge := k2_node_status_openBridge
theorem k6_target_open : k6_dependency.target.status = .openBridge := k4_status_openBridge
theorem k6_target_not_certified : ¬ Nonempty (ProofCertificate k6_dependency.target) := k4_no_promotion
end MCore
