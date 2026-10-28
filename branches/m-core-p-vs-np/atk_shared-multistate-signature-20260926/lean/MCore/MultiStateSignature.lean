import MCore.Signature

namespace MCore
namespace SharedSignature

structure MultiStateSignatureShape where
  Phase : Type
  related : Phase → Phase → Prop
  marked : Phase → Prop

structure ProblemManifestation
    (Problem : Type)
    (shape : MultiStateSignatureShape)
    (p : Problem) where
  Value : Type
  State : Type
  value : Value
  observable : State → Value
  phase : State → shape.Phase
  realizes :
    ∃ a b : State,
      a ≠ b ∧
      observable a = value ∧
      observable b = value ∧
      shape.related (phase a) (phase b)

structure SharedMultiStateSignature (Problem : Type) where
  shape : MultiStateSignatureShape
  manifestation : ∀ p : Problem, ProblemManifestation Problem shape p

def UniversalSharedMultiStateSignature (Problem : Type) : Prop :=
  Nonempty (SharedMultiStateSignature Problem)

theorem shared_shape_problem_specific_manifestations
    {Problem : Type}
    (S : SharedMultiStateSignature Problem) :
    ∃ shape : MultiStateSignatureShape,
      ∀ p : Problem,
        Nonempty (ProblemManifestation Problem shape p) := by
  refine ⟨S.shape, ?_⟩
  intro p
  exact ⟨S.manifestation p⟩

theorem universal_shared_signature_iff
    {Problem : Type} :
    UniversalSharedMultiStateSignature Problem ↔
      ∃ shape : MultiStateSignatureShape,
        ∀ p : Problem,
          Nonempty (ProblemManifestation Problem shape p) := by
  constructor
  · rintro ⟨S⟩
    exact shared_shape_problem_specific_manifestations S
  · rintro ⟨shape, h⟩
    classical
    refine ⟨{
      shape := shape
      manifestation := fun p => Classical.choice (h p)
    }⟩

#print axioms MCore.SharedSignature.shared_shape_problem_specific_manifestations
#print axioms MCore.SharedSignature.universal_shared_signature_iff

end SharedSignature
end MCore


namespace MCore
namespace SharedSignature

/-- Evidence is problem-local: it records observations supporting one
manifestation without asserting the endpoint theorem. -/
structure ManifestationEvidence
    {Problem : Type}
    {shape : MultiStateSignatureShape}
    {p : Problem}
    (M : ProblemManifestation Problem shape p) where
  Sample : Type
  observe : Sample → M.State
  covers_value :
    ∃ s : Sample, M.observable (observe s) = M.value
  covers_relation :
    ∃ s t : Sample,
      shape.related (M.phase (observe s)) (M.phase (observe t))

/-- A family of problem-specific manifestations of one common structural
shape, together with evidence for every manifestation. -/
structure UnifiedStructuralSignature (Problem : Type) where
  shared : SharedMultiStateSignature Problem
  evidence :
    ∀ p : Problem,
      ManifestationEvidence (shared.manifestation p)

/-- Each problem is allowed its own endpoint proposition and its own adapter.
The universal theorem does not identify the endpoints; it only factors them
through the common structural shape. -/
structure EndpointAdapter
    {Problem : Type}
    (U : UnifiedStructuralSignature Problem)
    (Endpoint : Problem → Prop) where
  promotes :
    ∀ p : Problem,
      ProblemManifestation Problem U.shared.shape p →
      ManifestationEvidence (U.shared.manifestation p) →
      Endpoint p

/-- Unified theorem: one common shape plus a certified adapter for every
problem yields every problem-specific endpoint. -/
theorem unified_signature_closes_all_endpoints
    {Problem : Type}
    (U : UnifiedStructuralSignature Problem)
    (Endpoint : Problem → Prop)
    (A : EndpointAdapter U Endpoint) :
    ∀ p : Problem, Endpoint p := by
  intro p
  exact A.promotes p (U.shared.manifestation p) (U.evidence p)

/-- The universal theorem is a transport theorem. Its material producer is
the pair consisting of an inhabitant of UnifiedStructuralSignature and an
EndpointAdapter. Evidence alone is not promoted to an endpoint. -/
def UnifiedTheoremProducer
    (Problem : Type)
    (Endpoint : Problem → Prop) : Prop :=
  ∃ U : UnifiedStructuralSignature Problem,
    Nonempty (EndpointAdapter U Endpoint)

theorem unified_theorem_producer_closes
    {Problem : Type}
    {Endpoint : Problem → Prop}
    (h : UnifiedTheoremProducer Problem Endpoint) :
    ∀ p : Problem, Endpoint p := by
  rcases h with ⟨U, ⟨A⟩⟩
  exact unified_signature_closes_all_endpoints U Endpoint A

#print axioms MCore.SharedSignature.unified_signature_closes_all_endpoints
#print axioms MCore.SharedSignature.unified_theorem_producer_closes

end SharedSignature
end MCore
