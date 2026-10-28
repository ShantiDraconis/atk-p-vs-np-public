import MCore.K3
namespace MCore
structure FrontierBridge where
  id : String
  prerequisite : CertNode
  target : CertNode
  status : SignatureStatus
def k3_frontier_bridge : FrontierBridge := { id := "K3_algebra_audit", prerequisite := k1_node, target := k3_gap_node, status := .openBridge }
theorem k3_frontier_open : k3_frontier_bridge.status = .openBridge := rfl
end MCore
