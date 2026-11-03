import MCore.P012.P012Core

namespace MCore
namespace P012

inductive FlowState where
  | open0
  | flowing
  | singularity
  | closed1
  deriving DecidableEq, Repr, BEq

def ComplexityFlow : Nat → FlowState
  | 0 => .open0
  | 1 => .flowing
  | _ => .closed1

def SurgeryFlow : FlowState → FlowState
  | .singularity => .open0
  | .flowing => .closed1
  | x => x

def SurgeryEstado : EstadoP012 → EstadoP012
  | .indet => .open0
  | .inf => .open0
  | x => x

theorem L15_flowing_closes :
    SurgeryFlow .flowing = .closed1 := rfl

theorem L16_singularity_removes :
    SurgeryFlow .singularity = .open0 := rfl

theorem L17_indet_to_open0 :
    SurgeryEstado .indet = .open0 := rfl

theorem L18_inf_to_open0 :
    SurgeryEstado .inf = .open0 := rfl

theorem L19_open0_idem :
    SurgeryEstado .open0 = .open0 := rfl

theorem L20_closed1_idem :
    SurgeryEstado .closed1 = .closed1 := rfl

theorem L21_idempotent_estado (e : EstadoP012) :
    SurgeryEstado (SurgeryEstado e) = SurgeryEstado e := by
  cases e <;> rfl

theorem L22_idempotent_flow (s : FlowState) :
    SurgeryFlow (SurgeryFlow s) = SurgeryFlow s := by
  cases s <;> rfl

/-- Normalization of the eight-state vocabulary.  The result stays inside the
same finite state space; this is the precise replacement for any informal
claim that a ninth state is impossible. -/
def normalize8 : State8 → State8
  | .q2_singularity => .q0_open
  | .q4_indet => .q0_open
  | .q5_inf => .q0_open
  | q => q

theorem normalize8_idempotent (q : State8) :
    normalize8 (normalize8 q) = normalize8 q := by
  cases q <;> rfl

end P012
end MCore
