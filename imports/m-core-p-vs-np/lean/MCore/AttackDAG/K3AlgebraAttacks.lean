import MCore.K3
namespace MCore
structure AlgebraAttack where
  id : String
  target : CertNode
  routeOnly : Bool
def k3_algebra_attack : AlgebraAttack := { id := "K3_status_promotion_attack", target := k3_gap_node, routeOnly := true }
theorem k3_attack_route_only : k3_algebra_attack.routeOnly = true := rfl
theorem k3_attack_cannot_promote : ¬ Nonempty (ProofCertificate k3_algebra_attack.target) := by intro h; rcases h with ⟨c⟩; exact k3_gap_not_proved c.status_proved
end MCore
