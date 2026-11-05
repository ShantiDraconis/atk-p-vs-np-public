import MCore.Real.P02G21G22Attack
import MCore.Real.P02DiagonalFrontier
import MCore.Real.P02KleeneBridge
import MCore.Real.P02UniversalDiagonalFirewall

namespace MCore
namespace Real
namespace P02LiveFrontierAfterFirewall

open CanonicalFinalProof
open P02G21G22Attack
open P02TerminalFrontier
open P02DiagonalFrontier
open P02KleeneBridge
open P02UniversalDiagonalFirewall

/-- The minimal live proposition after all current no-go results.
It is not weakened or strengthened by the firewall: it remains the exact
pointwise failure statement. -/
abbrev LiveG21Target : Prop :=
  G21Pointwise

theorem liveTarget_iff_p02 :
    LiveG21Target ↔ P02Target :=
  g21_pointwise_iff_p02_target

/-- A semantic diagonal family is a stronger producer sufficient for the live
target.  This is one-way on purpose; no converse is asserted. -/
theorem diagonalFamily_closes_liveTarget
    (D : DiagonalFamily) :
    LiveG21Target := by
  apply g21_pointwise_iff_p02_target.mpr
  exact diagonal_family_closes_p02 D

/-- Likewise the general Kleene/SAT realizer gap is a sufficient stronger
producer.  The previously refuted special compilers do not inhabit it. -/
theorem kleeneRealizer_closes_liveTarget
    (h : CanonicalSATKleeneRealizerGap) :
    LiveG21Target := by
  exact kleene_sat_bridge_closes_G21
    (Classical.choice
      (canonicalSATKleeneRealizerGap_to_D3KleeneSATBridgeGap h))

/-- The current universal no-go certificate coexists with the live target
without deciding it.  It only removes five invalid construction classes. -/
structure LiveFrontierCertificate where
  firewall : UniversalDiagonalRouteFirewall
  target : Prop
  target_eq : target = LiveG21Target

def liveFrontierCertificate : LiveFrontierCertificate where
  firewall := universalDiagonalRouteFirewall
  target := LiveG21Target
  target_eq := rfl

#print axioms MCore.Real.P02LiveFrontierAfterFirewall.liveTarget_iff_p02
#print axioms MCore.Real.P02LiveFrontierAfterFirewall.diagonalFamily_closes_liveTarget
#print axioms MCore.Real.P02LiveFrontierAfterFirewall.kleeneRealizer_closes_liveTarget
#print axioms MCore.Real.P02LiveFrontierAfterFirewall.liveFrontierCertificate

end P02LiveFrontierAfterFirewall
end Real
end MCore
