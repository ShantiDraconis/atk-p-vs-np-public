import MCore.Real.P02RejectionImageEscape
import MCore.Real.P02FinalRootConditional

namespace MCore
namespace Real
namespace P02RPADualConfirmation

open CanonicalFinalProof
open P02RejectionImageEscape
open P02ActiveBridgeClosure
open P02FinalRootConditional

/-- RPA certifies a transition, not one side in isolation. -/
structure RPATransition (Open Closed : Prop) where
  open_witness : Open
  closed_witness : Closed
  identity : Open ↔ Closed

/-- Active OPEN/CLOSED payloads are the same terminal proposition, but carry
separate source/destination witnesses in an RPA certificate. -/
abbrev OPEN_MATH : Prop := Endpoint
abbrev CLOSED_MATH : Prop := Endpoint
abbrev OPEN_BRIDGE : Prop := Endpoint
abbrev CLOSED_BRIDGE : Prop := Endpoint

def ActiveRPA : Prop := Nonempty (RPATransition OPEN_MATH CLOSED_MATH)

/-- A complete RPA transition is equivalent to a terminal endpoint inhabitant:
given Endpoint we can populate both source and destination; conversely any
transition contains an OPEN witness. -/
theorem activeRPA_nonempty_iff_endpoint :
    ActiveRPA ↔ Endpoint := by
  constructor
  · rintro ⟨cert⟩
    exact cert.open_witness
  · intro h
    exact ⟨{
      open_witness := h
      closed_witness := h
      identity := Iff.rfl
    }⟩

/-- Bridge view: same payload, same identity, no extra mathematical delta. -/
theorem openBridge_iff_openMath :
    OPEN_BRIDGE ↔ OPEN_MATH := Iff.rfl

theorem closedBridge_iff_closedMath :
    CLOSED_BRIDGE ↔ CLOSED_MATH := Iff.rfl

/-- MATH is the fixed point of the fully witnessed transition. -/
def MATH : Prop := ActiveRPA

/-- FINAL_ROOT and GLOBAL_EXTERNAL_CERTIFICATE are publication views of the
same fully witnessed RPA object. -/
abbrev FINAL_ROOT_RPA : Prop := MATH
abbrev GLOBAL_EXTERNAL_CERTIFICATE : Prop := FINAL_ROOT_RPA

theorem math_iff_endpoint :
    MATH ↔ Endpoint :=
  activeRPA_nonempty_iff_endpoint

theorem finalRoot_iff_math :
    FINAL_ROOT_RPA ↔ MATH := Iff.rfl

theorem globalExternal_iff_finalRoot :
    GLOBAL_EXTERNAL_CERTIFICATE ↔ FINAL_ROOT_RPA := Iff.rfl

/-- The requested five-view identity. -/
theorem rpa_five_view_identity :
    (MATH ↔ Endpoint) ∧
    (OPEN_BRIDGE ↔ OPEN_MATH) ∧
    (CLOSED_BRIDGE ↔ CLOSED_MATH) ∧
    (FINAL_ROOT_RPA ↔ MATH) ∧
    (GLOBAL_EXTERNAL_CERTIFICATE ↔ FINAL_ROOT_RPA) := by
  exact ⟨
    math_iff_endpoint,
    Iff.rfl,
    Iff.rfl,
    Iff.rfl,
    Iff.rfl
  ⟩

/-- Once the terminal endpoint is inhabited, the complete RPA certificate,
FINAL_ROOT view and GLOBAL_EXTERNAL_CERTIFICATE are all inhabited. -/
theorem endpoint_closes_all_rpa_views
    (h : Endpoint) :
    MATH ∧ FINAL_ROOT_RPA ∧ GLOBAL_EXTERNAL_CERTIFICATE := by
  have hm : MATH := (math_iff_endpoint).2 h
  exact ⟨hm, hm, hm⟩

/-- Conversely, the external certificate necessarily contains the terminal
mathematical witness; certification cannot manufacture it. -/
theorem global_external_contains_endpoint
    (h : GLOBAL_EXTERNAL_CERTIFICATE) :
    Endpoint := by
  exact (math_iff_endpoint).1 h

/-- Active external certificate closes the canonical separation root. -/
theorem global_external_closes_pneqnp
    (h : GLOBAL_EXTERNAL_CERTIFICATE) :
    PneqNP := by
  exact P02ActiveBridgeClosure.rejectImageEscape_closes_pneqnp
    (global_external_contains_endpoint h)

#print axioms MCore.Real.P02RPADualConfirmation.activeRPA_nonempty_iff_endpoint
#print axioms MCore.Real.P02RPADualConfirmation.rpa_five_view_identity
#print axioms MCore.Real.P02RPADualConfirmation.endpoint_closes_all_rpa_views
#print axioms MCore.Real.P02RPADualConfirmation.global_external_contains_endpoint

end P02RPADualConfirmation
end Real
end MCore
