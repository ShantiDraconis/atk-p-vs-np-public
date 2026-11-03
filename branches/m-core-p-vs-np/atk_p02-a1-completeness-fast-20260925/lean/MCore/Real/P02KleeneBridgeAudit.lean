import MCore.Real.P02KleeneSelfReferenceBridge

namespace MCore
namespace Real
namespace P02KleeneBridgeAudit

open CanonicalFinalProof
open P02DiagonalFrontier
open P02FinalAttack
open P02KleeneSelfReferenceBridge

/-- Any already-existing diagonal family yields a trivial Kleene bridge by
using the identity code transformer and ignoring the fixed-point equality.
This theorem is an audit result: the abstract bridge does not by itself reduce
the mathematical hardness of D3. -/
def diagonalFamilyToKleeneBridge
    (D : DiagonalFamily) :
    KleeneToSATBridge where
  compile := fun _ c => c
  compile_computable := fun _ => Computable.id
  self_semantics_to_diagonal := fun M _ _ => D.witness M

theorem diagonalFamily_implies_kleeneBridge :
    Nonempty DiagonalFamily → Nonempty KleeneToSATBridge := by
  intro h
  rcases h with ⟨D⟩
  exact ⟨diagonalFamilyToKleeneBridge D⟩

theorem kleeneBridge_implies_diagonalFamily :
    Nonempty KleeneToSATBridge → Nonempty DiagonalFamily := by
  intro h
  rcases h with ⟨B⟩
  exact ⟨B.toDiagonalFamily⟩

theorem kleeneBridge_iff_D3 :
    Nonempty KleeneToSATBridge ↔ D3SemanticSelfReference := by
  constructor
  · exact fun h => by
      rcases h with ⟨B⟩
      exact kleene_bridge_closes_D3 B
  · intro h
    rcases h with ⟨D⟩
    exact ⟨diagonalFamilyToKleeneBridge D⟩

#print axioms diagonalFamily_implies_kleeneBridge
#print axioms kleeneBridge_implies_diagonalFamily
#print axioms kleeneBridge_iff_D3

end P02KleeneBridgeAudit
end Real
end MCore
