import MCore.Real.P02FiniteDescriptorResidualCore
import MCore.Real.P02DiagonalOrbitCore

namespace MCore
namespace Real
namespace P02FiniteDescriptorOrbitResidual

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FailureNormalForms
open P02FiniteDescriptorReduction
open P02FiniteDescriptorResidualCore
open P02SemanticTransformerDichotomy
open P02DiagonalOrbitCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def DescriptorOrbitCorrect
    (D : FiniteDTMDescriptor) : Prop :=
  ConstantOrbitCorrectPattern D.toCandidate

/-- Final finite-descriptor residual after eliminating:
1. declared-clock failures,
2. mistakes on the canonical false/true constants,
3. any alignment appearing on either diagonal orbit from those constants. -/
def FiniteDescriptorOrbitResidual : Prop :=
  ∀ D : FiniteDTMDescriptor,
    DescriptorTotal D →
    DescriptorConstantCorrect D →
    DescriptorOrbitCorrect D →
      ∃ x : BitString,
        SemanticDisagreement D.toCandidate x

theorem orbitResidual_implies_residual
    (H : FiniteDescriptorOrbitResidual) :
    FiniteDescriptorResidual := by
  intro D hTotal hPattern
  rcases orbit_alignment_or_constant_orbit_correct
      D.toCandidate hTotal hPattern with hFalse | hRest
  · exact orbit_alignment_gives_semantic_disagreement
      D.toCandidate falseBits hFalse
  · rcases hRest with hTrue | hOrbit
    · exact orbit_alignment_gives_semantic_disagreement
        D.toCandidate trueBits hTrue
    · exact H D hTotal hPattern hOrbit

theorem residual_implies_orbitResidual
    (H : FiniteDescriptorResidual) :
    FiniteDescriptorOrbitResidual := by
  intro D hTotal hPattern _
  exact H D hTotal hPattern

theorem orbitResidual_iff_residual :
    FiniteDescriptorOrbitResidual ↔
      FiniteDescriptorResidual := by
  constructor
  · exact orbitResidual_implies_residual
  · exact residual_implies_orbitResidual

theorem orbitResidual_iff_universalFailure :
    FiniteDescriptorOrbitResidual ↔
      UniversalFailure SATTarget := by
  exact orbitResidual_iff_residual.trans
    residual_iff_universalFailure

theorem orbitResidual_closes_internal_endpoint
    (H : FiniteDescriptorOrbitResidual) :
    PneqNP :=
  residual_closes_internal_endpoint
    (orbitResidual_implies_residual H)

#print axioms MCore.Real.P02FiniteDescriptorOrbitResidual.orbitResidual_implies_residual
#print axioms MCore.Real.P02FiniteDescriptorOrbitResidual.orbitResidual_iff_residual
#print axioms MCore.Real.P02FiniteDescriptorOrbitResidual.orbitResidual_iff_universalFailure
#print axioms MCore.Real.P02FiniteDescriptorOrbitResidual.orbitResidual_closes_internal_endpoint

end P02FiniteDescriptorOrbitResidual
end Real
end MCore
