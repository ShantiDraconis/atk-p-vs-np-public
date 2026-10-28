import MCore.K7

namespace MCore

namespace ComplexityDecomposition

variable {α : Type}

/-- Reconstruct a decomposition from its three certified projections. -/
def reconstruct (x : ComplexityDecomposition α) : ComplexityDecomposition α :=
  ComplexityDecomposition.mk (projectReal x) (projectImag x) (projectIndeterminate x)

@[simp] theorem reconstruct_eq (x : ComplexityDecomposition α) : reconstruct x = x := by
  cases x
  rfl

/-- Equality of all three components determines equality of decompositions. -/
theorem ext_components {x y : ComplexityDecomposition α}
    (hr : projectReal x = projectReal y)
    (hi : projectImag x = projectImag y)
    (hu : projectIndeterminate x = projectIndeterminate y) : x = y := by
  cases x with
  | mk xr xi xu =>
    cases y with
    | mk yr yi yu =>
      simp only [projectReal, projectImag, projectIndeterminate] at hr hi hu
      cases hr
      cases hi
      cases hu
      rfl

/-- Equality of projection triples forces equality of decompositions. This is
    the injectivity property stated without importing an external Function API. -/
theorem projection_injective {x y : ComplexityDecomposition α}
    (h : (projectReal x, projectImag x, projectIndeterminate x) =
         (projectReal y, projectImag y, projectIndeterminate y)) : x = y := by
  exact ext_components
    (congrArg (fun p => p.1) h)
    (congrArg (fun p => p.2.1) h)
    (congrArg (fun p => p.2.2) h)

end ComplexityDecomposition

/-- K8 certifies only internal decomposition algebra. It remains separate from
    the unresolved classical P-vs-NP bridge. -/
def k8_internal_node : CertNode :=
  { status := .openBridge
    statement := ∀ {α : Type} (x : ComplexityDecomposition α),
      ComplexityDecomposition.reconstruct x = x }

theorem k8_statement_valid : k8_internal_node.statement := by
  intro α x
  exact ComplexityDecomposition.reconstruct_eq x

theorem k8_status_openBridge : k8_internal_node.status = .openBridge := rfl

theorem k8_status_not_proved : k8_internal_node.status ≠ .provedProperty := by
  intro h
  cases h

theorem k8_not_certified : ¬ Nonempty (ProofCertificate k8_internal_node) := by
  intro h
  rcases h with ⟨hcert⟩
  exact k8_status_not_proved hcert.status_proved

theorem k8_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

end MCore
