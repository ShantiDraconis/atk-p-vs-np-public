import MCore.Real.PNPDiscovery.BarrierPressure
import MCore.Real.P02ExactDiagonalFrontier
import MCore.Real.P02TotalCandidateKleeneReduction
import MCore.Real.PNPDiscovery.NormalizedUniversalPrerequisites
import MCore.Real.PNPDiscovery.TransitionShapeFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02ExactDiagonalFrontier
open P02TotalCandidateKleeneReduction

/-- Exact global material min-cut of the current repository model.
No method/barrier/infrastructure obligation is stored here. -/
structure ExactPNPMaterialMinCut where
  satInNP : SATInNPPhysicalGap
  separation : TotalExactDiagonalProducer

theorem exactMaterialMinCut_closes
    (P : ExactPNPMaterialMinCut) :
    PneqNP := by
  have hNP := physical_gap_to_sat_in_np P.satInNP
  have hSep :=
    total_exact_diagonal_implies_universal_failure
      P.separation
  exact target_failure_implies_p_ne_np hNP hSep

/-- Separation-side open math is exactly one proposition: the exact diagonal
producer.  It is equivalent to the canonical SAT universal-failure endpoint,
so it must not be counted as an easier bridge. -/
def ExactSeparationOpenAtom : Prop :=
  TotalExactDiagonalProducer

theorem exactSeparationOpenAtom_iff_endpoint :
    ExactSeparationOpenAtom ↔
      SATSeparationGap := by
  exact total_exact_diagonal_iff_universal_failure

/-- Existing Kleene route is only a sufficient METHOD route into the exact
material atom. -/
theorem totalKleeneBridge_to_exactSeparation
    (B : TotalCandidateKleeneBridge) :
    ExactSeparationOpenAtom := by
  apply universal_failure_implies_total_exact_diagonal
  exact total_candidate_kleene_implies_universal_failure B

/-- The normalized universal/self-reference infrastructure is explicitly
classified as method infrastructure.  Merely inhabiting it is not declared
to imply separation.  One still needs a semantic theorem turning that
infrastructure into an exact SAT flip for every total candidate. -/
def NormalizedInfrastructureSemanticClosure : Prop :=
  CurrentSelfReferencePrerequisitesGap →
    ExactSeparationOpenAtom

/-- Layout-shape work is also a route-level frontier.  Even closing this
reducible counting statement does not by itself inhabit the material atom. -/
def LayoutRouteMechanicalOpenAtom : Prop :=
  EqualRadiusTransitionShapeGap

/-- Canonical route ledger: one material separation atom, with two explored
method routes. -/
structure ExactOpenMathLedger where
  materialSATInNP : Prop := SATInNPPhysicalGap
  materialSeparation : Prop := ExactSeparationOpenAtom
  layoutMechanical : Prop := LayoutRouteMechanicalOpenAtom
  normalizedInfrastructure : Prop := CurrentSelfReferencePrerequisitesGap
  semanticSelfReferenceClosure : Prop :=
    NormalizedInfrastructureSemanticClosure

def exactOpenMathLedger : ExactOpenMathLedger := {}

/-- Only the first two ledger fields are required by the endpoint.
The remaining fields classify possible proof strategies. -/
theorem only_material_fields_close
    (hNP : exactOpenMathLedger.materialSATInNP)
    (hSep : exactOpenMathLedger.materialSeparation) :
    PneqNP :=
  exactMaterialMinCut_closes
    { satInNP := hNP
      separation := hSep }

#print axioms MCore.Real.PNPDiscovery.exactMaterialMinCut_closes
#print axioms MCore.Real.PNPDiscovery.exactSeparationOpenAtom_iff_endpoint
#print axioms MCore.Real.PNPDiscovery.totalKleeneBridge_to_exactSeparation
#print axioms MCore.Real.PNPDiscovery.only_material_fields_close

end PNPDiscovery
end Real
end MCore
