import MCore.P012.P012PrimeTransitionBoundary
import MCore.P012.P012Interpretation

namespace MCore
namespace P012

/-- Observational interpretation from signed-third orientation to the P012
metamodel. This does not create any mathematical producer. -/
def orientationToP012 : Orientation → EstadoP012
  | .negative => .open0
  | .neutral => .indet
  | .positive => .closed1

theorem negative_maps_open :
    orientationToP012 .negative = .open0 := rfl

theorem neutral_maps_indet :
    orientationToP012 .neutral = .indet := rfl

theorem positive_maps_closed :
    orientationToP012 .positive = .closed1 := rfl

theorem negTwo_observes_open :
    orientationToP012 (orientation negTwoThirds) = .open0 := by
  rw [orientation_negTwo]
  rfl

theorem zero_observes_indet :
    orientationToP012 (orientation zeroThird) = .indet := by
  rw [orientation_zero]
  rfl

theorem three_observes_closed :
    orientationToP012 (orientation threeThirds) = .closed1 := by
  rw [orientation_three]
  rfl

/-- Full observational composition into the pipeline-state vocabulary. -/
def signedThirdPipelineState (s : ThirdState) : PipelineState :=
  interpretP012 (orientationToP012 (orientation s))

theorem negTwo_pipeline_open :
    signedThirdPipelineState negTwoThirds = .open := by
  simp [signedThirdPipelineState, orientation_negTwo, orientationToP012,
    interpretP012]

theorem zero_pipeline_unresolved :
    signedThirdPipelineState zeroThird = .unresolved := by
  simp [signedThirdPipelineState, orientation_zero, orientationToP012,
    interpretP012]

theorem three_pipeline_closed_label :
    signedThirdPipelineState threeThirds = .closed := by
  simp [signedThirdPipelineState, orientation_three, orientationToP012,
    interpretP012]

/-
Important firewall:
A closed signed-third pipeline label is only a metamodel observation.
There is deliberately no theorem from this fact to P01ConstructionGap,
G21Pointwise, P02Target, OfficialPneqNP, or FinalExternalCertificate.
-/

#print axioms MCore.P012.negTwo_pipeline_open
#print axioms MCore.P012.zero_pipeline_unresolved
#print axioms MCore.P012.three_pipeline_closed_label

end P012
end MCore
