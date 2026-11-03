import MCore.Real.TerminalGapP012
import MCore.Real.DivZeroP012
import MCore.Real.FinalExternalTwoGap

namespace MCore
namespace Real
namespace AdaptacaoMinhaLogicaFinal

open P01FinalCertificate
open P02G21G22Attack
open FinalExternalTwoGap
open DivZeroP012
open TerminalGapP012

/-- Auxiliary flow states.  These are bookkeeping states only; they do not
manufacture either terminal proof. -/
inductive FlowState
| open0
| flowing
| singularity
| closed1
deriving DecidableEq, Repr

/-- Surgery removes singular/undefined bookkeeping states back to open0. -/
def SurgeryFlow : FlowState → FlowState
| .singularity => .open0
| .flowing     => .closed1
| x            => x

/-- The symbolic division surgery keeps only open0/closed1. -/
def SurgeryEstado : DivState → DivState
| .indet => .open0
| .inf   => .open0
| x      => x

@[simp] theorem surgery_indet_open :
    SurgeryEstado .indet = .open0 := rfl

@[simp] theorem surgery_inf_open :
    SurgeryEstado .inf = .open0 := rfl

@[simp] theorem surgery_open_idem :
    SurgeryEstado .open0 = .open0 := rfl

@[simp] theorem surgery_closed_idem :
    SurgeryEstado .closed1 = .closed1 := rfl

theorem surgeryEstado_idempotent
    (s : DivState) :
    SurgeryEstado (SurgeryEstado s) = SurgeryEstado s := by
  cases s <;> rfl

theorem surgeryFlow_idempotent
    (s : FlowState) :
    SurgeryFlow (SurgeryFlow s) = SurgeryFlow s := by
  cases s <;> rfl

/-- A monotone auxiliary W-functional.  This is deliberately weaker than G21. -/
structure PerelmanW where
  W : Nat → Nat
  mono : ∀ t, W t ≤ W (t + 1)

/-- Concrete monotone example W(t)=t^2+100. -/
def W_SAT : PerelmanW where
  W := fun t => t * t + 100
  mono := by
    intro t
    omega

theorem W_SAT_mono (t : Nat) :
    W_SAT.W t ≤ W_SAT.W (t + 1) := by
  exact W_SAT.mono t

/-- The missing mathematical content must be an explicit bridge from the
auxiliary W-object to the real G21Pointwise theorem.  Having W alone does not
provide such a bridge. -/
def G21EntropyBridge : Prop :=
  ∀ W : PerelmanW, G21Pointwise

/-- If a real bridge is proved, the concrete W_SAT object closes G21. -/
theorem W_SAT_closes_G21
    (hBridge : G21EntropyBridge) :
    G21Pointwise := by
  exact hBridge W_SAT

/-- P01 stays tied to the repository's actual machine-construction endpoint. -/
def P01Built : Prop :=
  P01ConstructionGap

/-- G21Built is the real lower-bound theorem, not merely monotonicity of W. -/
def G21Built : Prop :=
  G21Pointwise

/-- Exact rigid core under the real repository endpoints. -/
abbrev RigidCore : Prop :=
  P01Built ∧ G21Built

theorem rigidCore_iff_real_terminal_pair :
    RigidCore ↔ FinalExternalTwoGap := by
  rfl

/-- P01 only: one terminal producer is present, so the symbolic pair remains
open0. -/
theorem p01_only_stays_partial
    (hP01 : P01ConstructionGap) :
    terminalPairState
      (classifyP01 (some hP01))
      (classifyG21 none) = .open0 := by
  exact p01_alone_is_partial hP01

/-- G21 only: symmetric partial state. -/
theorem g21_only_stays_partial
    (hG21 : G21Pointwise) :
    terminalPairState
      (classifyP01 none)
      (classifyG21 (some hG21)) = .open0 := by
  exact g21_alone_is_partial hG21

/-- Both actual terminal inhabitants produce the rigid closed1 state. -/
theorem both_real_close_symbolic_state
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    terminalPairState
      (classifyP01 (some hP01))
      (classifyG21 (some hG21)) = .closed1 := by
  exact both_real_are_rigid hP01 hG21

/-- Final proof-level promotion.  The W-functional participates only through a
separately proved G21EntropyBridge; it is never substituted for G21Pointwise. -/
def final_from_p01_and_W_bridge
    (hP01 : P01ConstructionGap)
    (hBridge : G21EntropyBridge) :
    FinalExternalTwoGap :=
  ⟨hP01, W_SAT_closes_G21 hBridge⟩

#print axioms MCore.Real.AdaptacaoMinhaLogicaFinal.W_SAT_mono
#print axioms MCore.Real.AdaptacaoMinhaLogicaFinal.W_SAT_closes_G21
#print axioms MCore.Real.AdaptacaoMinhaLogicaFinal.rigidCore_iff_real_terminal_pair
#print axioms MCore.Real.AdaptacaoMinhaLogicaFinal.both_real_close_symbolic_state
#print axioms MCore.Real.AdaptacaoMinhaLogicaFinal.final_from_p01_and_W_bridge

end AdaptacaoMinhaLogicaFinal
end Real
end MCore
