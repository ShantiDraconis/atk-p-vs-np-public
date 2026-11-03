import MCore.Real.P012FailClosed
import MCore.Real.DivZeroP012
import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalTwoGap

namespace MCore
namespace Real
namespace TerminalGapP012

open P01FinalCertificate
open P02G21G22Attack
open FinalExternalTwoGap
open DivZeroP012

/-- Fail-closed state of the P01 terminal producer. -/
inductive P01GapState
| open
| closed
deriving DecidableEq, Repr

/-- Fail-closed state of the G21 terminal producer. -/
inductive G21GapState
| open
| closed
deriving DecidableEq, Repr

/-- P01 is closed only when an actual P01ConstructionGap inhabitant is supplied. -/
def classifyP01 (h : Option P01ConstructionGap) : P01GapState :=
  match h with
  | none => .open
  | some _ => .closed

/-- G21 is closed only when an actual G21Pointwise inhabitant is supplied. -/
def classifyG21 (h : Option G21Pointwise) : G21GapState :=
  match h with
  | none => .open
  | some _ => .closed

@[simp] theorem classifyP01_none :
    classifyP01 none = .open := rfl

@[simp] theorem classifyP01_some
    (h : P01ConstructionGap) :
    classifyP01 (some h) = .closed := rfl

@[simp] theorem classifyG21_none :
    classifyG21 none = .open := rfl

@[simp] theorem classifyG21_some
    (h : G21Pointwise) :
    classifyG21 (some h) = .closed := rfl

/-- Exact P01 closure criterion: no inhabitant, no closure. -/
theorem p01_closed_iff_exists_real :
    (∃ h : P01ConstructionGap, classifyP01 (some h) = .closed) ↔
      Nonempty P01ConstructionGap := by
  constructor
  · rintro ⟨h, _⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    exact ⟨h, rfl⟩

/-- Exact G21 closure criterion: no inhabitant, no closure. -/
theorem g21_closed_iff_exists_real :
    (∃ h : G21Pointwise, classifyG21 (some h) = .closed) ↔
      Nonempty G21Pointwise := by
  constructor
  · rintro ⟨h, _⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    exact ⟨h, rfl⟩

/-- Numeric P012 view of the P01 terminal gate.
open = 0/1, closed = 1/1. -/
def p01DivState : P01GapState → DivState
| .open => .open0
| .closed => .closed1

/-- Numeric P012 view of the G21 terminal gate.
open = 0/1, closed = 1/1. -/
def g21DivState : G21GapState → DivState
| .open => .open0
| .closed => .closed1

@[simp] theorem p01_open_not_rigid :
    ¬ IsRigidCore (p01DivState .open) := by
  simp [p01DivState, IsRigidCore]

@[simp] theorem p01_closed_is_rigid :
    IsRigidCore (p01DivState .closed) := by
  simp [p01DivState, IsRigidCore]

@[simp] theorem g21_open_not_rigid :
    ¬ IsRigidCore (g21DivState .open) := by
  simp [g21DivState, IsRigidCore]

@[simp] theorem g21_closed_is_rigid :
    IsRigidCore (g21DivState .closed) := by
  simp [g21DivState, IsRigidCore]

/-- AND semantics for the two real terminal gaps. -/
def terminalPairState
    (p : P01GapState)
    (g : G21GapState) : DivState :=
  FinalTwoGapState (p01DivState p) (g21DivState g)

@[simp] theorem terminalPair_open_open :
    terminalPairState .open .open = .open0 := by
  simp [terminalPairState, p01DivState, g21DivState, FinalTwoGapState]

@[simp] theorem terminalPair_closed_open :
    terminalPairState .closed .open = .open0 := by
  simp [terminalPairState, p01DivState, g21DivState, FinalTwoGapState]

@[simp] theorem terminalPair_open_closed :
    terminalPairState .open .closed = .open0 := by
  simp [terminalPairState, p01DivState, g21DivState, FinalTwoGapState]

@[simp] theorem terminalPair_closed_closed :
    terminalPairState .closed .closed = .closed1 := by
  simp [terminalPairState, p01DivState, g21DivState, FinalTwoGapState]

/-- Rigid-core characterization: 2/2 closes iff both terminal gaps are closed. -/
theorem terminalPair_closed_iff
    (p : P01GapState) (g : G21GapState) :
    terminalPairState p g = .closed1 ↔
      p = .closed ∧ g = .closed := by
  cases p <;> cases g <;> simp [terminalPairState, p01DivState, g21DivState, FinalTwoGapState]

/-- Actual proof-level promotion: both inhabitants are required. -/
def realTerminalPair
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    FinalExternalTwoGap :=
  ⟨hP01, hG21⟩

/-- P01 alone cannot produce the final pair. -/
theorem p01_alone_is_partial
    (hP01 : P01ConstructionGap) :
    terminalPairState (classifyP01 (some hP01)) (classifyG21 none) = .open0 := by
  rfl

/-- G21 alone cannot produce the final pair. -/
theorem g21_alone_is_partial
    (hG21 : G21Pointwise) :
    terminalPairState (classifyP01 none) (classifyG21 (some hG21)) = .open0 := by
  rfl

/-- Both real inhabitants yield the rigid 1/1 state. -/
theorem both_real_are_rigid
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    terminalPairState (classifyP01 (some hP01)) (classifyG21 (some hG21)) = .closed1 := by
  rfl

#print axioms MCore.Real.TerminalGapP012.p01_closed_iff_exists_real
#print axioms MCore.Real.TerminalGapP012.g21_closed_iff_exists_real
#print axioms MCore.Real.TerminalGapP012.terminalPair_closed_iff
#print axioms MCore.Real.TerminalGapP012.realTerminalPair
#print axioms MCore.Real.TerminalGapP012.both_real_are_rigid

end TerminalGapP012
end Real
end MCore
