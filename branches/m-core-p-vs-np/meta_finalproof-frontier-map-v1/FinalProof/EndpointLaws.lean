import FinalProof.EndpointProofTarget

namespace FinalProof

theorem pnp003_has_P01MachineConstruction
    (r : PNP003Requirements) (h : r.closed) :
    r.P01MachineConstruction := h.1

theorem pnp003_has_p01_closed_no_hypothesis
    (r : PNP003Requirements) (h : r.closed) :
    r.p01_closed_no_hypothesis := h.2.1

theorem pnp003_has_semantic_self_embedding
    (r : PNP003Requirements) (h : r.closed) :
    r.semantic_self_embedding_witness := h.2.2.1

theorem pnp003_has_pointwise_universal_obstruction
    (r : PNP003Requirements) (h : r.closed) :
    r.pointwise_universal_obstruction := h.2.2.2.1

theorem pnp003_has_size_time_closure
    (r : PNP003Requirements) (h : r.closed) :
    r.size_time_closure := h.2.2.2.2

theorem pnp003_all_requirements_iff
    (r : PNP003Requirements) :
    r.closed ↔
      r.P01MachineConstruction ∧
      r.p01_closed_no_hypothesis ∧
      r.semantic_self_embedding_witness ∧
      r.pointwise_universal_obstruction ∧
      r.size_time_closure := by
  rfl

end FinalProof
