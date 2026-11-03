import MCore.Real.P02ClockedDiagonalCompiler

namespace MCore
namespace Real
namespace P02CandidateCodingBoundary

open CanonicalFinalProof
open P02ClockedDiagonalCompiler

/-- Optional stronger boundary for an effective self-reference route.
No inhabitant is asserted: the current hardened candidate structure contains
higher-order machine data and a polynomial proof, so a faithful finite code
must be constructed explicitly rather than assumed. -/
structure CandidateCodingInterface where
  encodeCandidate : PolyDTMCandidate → BitString
  faithful :
    ∀ {M₁ M₂ : PolyDTMCandidate},
      encodeCandidate M₁ = encodeCandidate M₂ →
      M₁ = M₂

def CandidateCodingGap : Prop :=
  Nonempty CandidateCodingInterface

/-- Universal simulation boundary over a supplied faithful coding. -/
structure UniversalSimulationInterface
    (C : CandidateCodingInterface) where
  evalEncoded : BitString → BitString → Bool
  simTime : TimeBound
  simTime_poly : PolynomialTimeBound simTime
  correct :
    ∀ (M : PolyDTMCandidate) (x : BitString),
      evalEncoded (C.encodeCandidate M) x =
        declaredAcceptBit M x

def UniversalSimulationGap : Prop :=
  ∃ C : CandidateCodingInterface,
    Nonempty (UniversalSimulationInterface C)

/-- Effective diagonal infrastructure packages coding plus universal
simulation. It is intentionally weaker than SameInputClosure: no theorem here
manufactures a self-referential SAT instance. -/
structure EffectiveDiagonalInfrastructure where
  coding : CandidateCodingInterface
  simulation : UniversalSimulationInterface coding

def EffectiveDiagonalInfrastructureGap : Prop :=
  Nonempty EffectiveDiagonalInfrastructure

theorem effectiveInfrastructure_has_coding
    (h : EffectiveDiagonalInfrastructureGap) :
    CandidateCodingGap := by
  rcases h with ⟨E⟩
  exact ⟨E.coding⟩

theorem effectiveInfrastructure_has_simulation
    (h : EffectiveDiagonalInfrastructureGap) :
    UniversalSimulationGap := by
  rcases h with ⟨E⟩
  exact ⟨E.coding, ⟨E.simulation⟩⟩

/-
No arrow
  EffectiveDiagonalInfrastructureGap -> SameInputClosure
is provided. That missing arrow is precisely the self-reference / same-input
mathematical bridge.
-/

#print axioms MCore.Real.P02CandidateCodingBoundary.effectiveInfrastructure_has_coding
#print axioms MCore.Real.P02CandidateCodingBoundary.effectiveInfrastructure_has_simulation

end P02CandidateCodingBoundary
end Real
end MCore
