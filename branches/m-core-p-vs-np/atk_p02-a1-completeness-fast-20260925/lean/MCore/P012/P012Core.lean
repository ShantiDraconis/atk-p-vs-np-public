import Std

namespace MCore
namespace P012

/-- Four semantic states of the P012 classifier.  This layer is metamathematical:
it classifies pipeline states and never manufactures a mathematical endpoint. -/
inductive EstadoP012 where
  | open0
  | closed1
  | indet
  | inf
  deriving DecidableEq, Repr, BEq

/-- Numeric classifier used by the P012 metatheory.
Only a nonzero diagonal a=b enters closed1. -/
def classifyP012 (a b : Nat) : EstadoP012 :=
  if b = 0 then
    if a = 0 then .indet else .inf
  else if a = 0 then
    .open0
  else if a = b then
    .closed1
  else
    .open0

def IsRigidCore (s : EstadoP012) : Prop :=
  s = .closed1

theorem L01_zero_over_nonzero_open0
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 0 n = .open0 := by
  simp [classifyP012, hn]

theorem L02_n_over_n_closed1
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 n n = .closed1 := by
  simp [classifyP012, hn]

theorem L03_zero_over_zero_indet :
    classifyP012 0 0 = .indet := by
  simp [classifyP012]

theorem L04_nonzero_over_zero_inf
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 n 0 = .inf := by
  simp [classifyP012, hn]

theorem L05_open_never_closed :
    EstadoP012.open0 ≠ .closed1 := by
  decide

theorem L06_indet_never_closed :
    EstadoP012.indet ≠ .closed1 := by
  decide

theorem L07_inf_never_closed :
    EstadoP012.inf ≠ .closed1 := by
  decide

/-- Converse characterization: closed1 is reached exactly by a nonzero
numeric diagonal. -/
theorem L08_only_n_over_n_enters_core
    (a b : Nat)
    (h : IsRigidCore (classifyP012 a b)) :
    a = b ∧ b ≠ 0 := by
  unfold IsRigidCore at h
  unfold classifyP012 at h
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 0 <;> simp [ha] at h
  · by_cases ha0 : a = 0
    · simp [hb, ha0] at h
    · by_cases hab : a = b
      · exact ⟨hab, hb⟩
      · simp [hb, ha0, hab] at h

/-- Eight-state control vocabulary for the metamathematical automaton.
These are labels only; none is a proof of a Millennium-problem endpoint. -/
inductive State8 where
  | q0_open
  | q1_flowing
  | q2_singularity
  | q3_closed
  | q4_indet
  | q5_inf
  | q6_check
  | q7_accept
  deriving DecidableEq, Repr, BEq

def state8ToP012 : State8 → EstadoP012
  | .q0_open => .open0
  | .q1_flowing => .open0
  | .q2_singularity => .inf
  | .q3_closed => .closed1
  | .q4_indet => .indet
  | .q5_inf => .inf
  | .q6_check => .open0
  | .q7_accept => .closed1

theorem q7_maps_closed :
    state8ToP012 .q7_accept = .closed1 := rfl

theorem q0_maps_open :
    state8ToP012 .q0_open = .open0 := rfl

end P012
end MCore
