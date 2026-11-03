import MCore.Real.PNPDiscovery.TerminalStateFrontier
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction

/-- Finite tape window visible to a single-tape machine within a bounded
number of moves. -/
structure TapeWindow (Symbol : Type) where
  left  : List Symbol
  head  : Symbol
  right : List Symbol
  deriving Repr, DecidableEq

def tapeWindow {Symbol : Type}
    (radius : Nat)
    (t : Tape Symbol) :
    TapeWindow Symbol :=
  { left := t.left.take radius
    head := t.head
    right := t.right.take radius }

def TapeWindowEq {Symbol : Type}
    (radius : Nat)
    (a b : Tape Symbol) : Prop :=
  tapeWindow radius a = tapeWindow radius b

@[simp] theorem tapeWindowEq_zero_iff {Symbol : Type}
    (a b : Tape Symbol) :
    TapeWindowEq 0 a b ↔ a.head = b.head := by
  simp [TapeWindowEq, tapeWindow, TapeWindow.ext_iff]

/-- One physical TM step consumes at most one unit of observable tape radius.
This is the fundamental locality law behind the read-cone construction. -/
theorem step_preserves_smaller_window
    {State Symbol : Type}
    (M : TM State Symbol)
    (fuel : Nat)
    (a b : Configuration State Symbol)
    (hState : a.state = b.state)
    (hWindow : TapeWindowEq (fuel + 1) a.tape b.tape) :
    (M.step a).state = (M.step b).state ∧
      TapeWindowEq fuel (M.step a).tape (M.step b).tape := by
  subst hState
  unfold TapeWindowEq tapeWindow at hWindow
  cases a with
  | mk qa ta =>
    cases b with
    | mk qb tb =>
      simp only at *
      have hHead : ta.head = tb.head := by
        exact congrArg TapeWindow.head hWindow
      cases ta with
      | mk la ha ra =>
        cases tb with
        | mk lb hb rb =>
          simp only at hHead
          subst hb
          cases htr : M.transition qa ha with
          | mk p dir =>
            cases p with
            | mk q' s' =>
              cases dir <;>
                cases la <;>
                cases lb <;>
                cases ra <;>
                cases rb <;>
                simp [TM.step, htr, TapeWindowEq, tapeWindow] at hWindow ⊢

/-- Bounded execution locality: equal initial states plus an equal radius-fuel
window force the same terminal control state after [fuel] evaluation steps.
Halting cannot desynchronize the runs because it depends only on control state. -/
theorem run_state_local
    {State Symbol : Type}
    (M : TM State Symbol) :
    ∀ fuel : Nat,
    ∀ a b : Configuration State Symbol,
      a.state = b.state →
      TapeWindowEq fuel a.tape b.tape →
      (M.run fuel a).state = (M.run fuel b).state := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b hState _
      simpa [TM.run] using hState
  | succ fuel ih =>
      intro a b hState hWindow
      have hHalt :
          M.halting a.state = M.halting b.state := by
        rw [hState]
      by_cases ha : M.halting a.state = true
      · have hb : M.halting b.state = true := by
          rw [← hHalt]
          exact ha
        simp [TM.run, ha, hb, hState]
      · have hb : M.halting b.state = false := by
          cases hval : M.halting b.state <;> simp_all
        have hStep :=
          step_preserves_smaller_window
            M fuel a b hState hWindow
        simp only [TM.run, ha, hb]
        exact ih (M.step a) (M.step b) hStep.1 hStep.2

/-- For canonical bitstring inputs, agreement on the first [fuel+1] input
symbols is enough to make the initial radius-fuel tape windows equal. -/
theorem initialTape_window_of_prefix
    (fuel : Nat)
    (x y : BitString)
    (hPrefix : x.take (fuel + 1) = y.take (fuel + 1)) :
    TapeWindowEq fuel (inputTape x) (inputTape y) := by
  cases x with
  | nil =>
      cases y with
      | nil =>
          simp [TapeWindowEq, tapeWindow, inputTape]
      | cons b bs =>
          simp at hPrefix
  | cons a as =>
      cases y with
      | nil =>
          simp at hPrefix
      | cons b bs =>
          simp [TapeWindowEq, tapeWindow, inputTape] at hPrefix ⊢
          exact ⟨hPrefix.1, by
            have htail := congrArg List.tail hPrefix
            simpa using htail⟩

/-- Candidate read-cone theorem.  On equal-length inputs, the declared clock
is identical; if their first T(n)+1 bits agree, the deterministic candidate
reaches the same terminal control state. -/
theorem terminalState_of_prefix
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length = y.length)
    (hPrefix :
      x.take (M.timeBound x.length + 1) =
        y.take (M.timeBound x.length + 1)) :
    terminalState M x = terminalState M y := by
  unfold terminalState
  have hT :
      M.timeBound x.length = M.timeBound y.length := by
    rw [hLen]
  rw [← hT]
  apply run_state_local
    M.machine
    (M.timeBound x.length)
    (initialTMConfig M.machine x)
    (initialTMConfig M.machine y)
  · rfl
  · exact initialTape_window_of_prefix
      (M.timeBound x.length) x y hPrefix

/-- Concrete prefix read cone for the canonical single-tape model. -/
def ReadConePrefix
    (M : PolyDTMCandidate)
    (x : BitString) : Nat :=
  M.timeBound x.length + 1

/-- The terminal-state observable factors through the finite read cone,
provided input length is fixed. -/
theorem readCone_invisibility
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length = y.length)
    (hCone :
      x.take (ReadConePrefix M x) =
        y.take (ReadConePrefix M x)) :
    terminalState M x = terminalState M y := by
  exact terminalState_of_prefix M x y hLen hCone


/-- Equal total input length was stronger than necessary.  For total
candidates, agreement through the smaller declared clock suffices: the run
with the smaller clock has already halted, and the larger-fuel run stutters
thereafter. -/
theorem terminalState_of_shared_min_cone
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (hPrefix :
      x.take (Nat.min (M.timeBound x.length) (M.timeBound y.length) + 1) =
        y.take (Nat.min (M.timeBound x.length) (M.timeBound y.length) + 1)) :
    terminalState M x = terminalState M y := by
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  by_cases hxy : tx ≤ ty
  · have hmin : Nat.min tx ty = tx := Nat.min_eq_left hxy
    have hp :
        x.take (tx + 1) = y.take (tx + 1) := by
      simpa [tx, ty, hmin] using hPrefix
    have hLocal :
        (M.machine.run tx (initialTMConfig M.machine x)).state =
          (M.machine.run tx (initialTMConfig M.machine y)).state := by
      exact run_state_local
        M.machine tx
        (initialTMConfig M.machine x)
        (initialTMConfig M.machine y)
        rfl
        (initialTape_window_of_prefix tx x y hp)
    have hHaltX :
        M.machine.halting
          (M.machine.run tx (initialTMConfig M.machine x)).state = true := by
      exact hTotal x
    have hHaltY :
        M.machine.halting
          (M.machine.run tx (initialTMConfig M.machine y)).state = true := by
      rw [← hLocal]
      exact hHaltX
    have hExtend :
        M.machine.run ty (initialTMConfig M.machine y) =
          M.machine.run tx (initialTMConfig M.machine y) := by
      exact MachineRunLemmas.run_to_larger_fuel_of_halt
        M.machine
        (initialTMConfig M.machine y)
        (M.machine.run tx (initialTMConfig M.machine y))
        hxy
        rfl
        hHaltY
    unfold terminalState
    change
      (M.machine.run tx (initialTMConfig M.machine x)).state =
        (M.machine.run ty (initialTMConfig M.machine y)).state
    rw [hExtend]
    exact hLocal
  · have hyx : ty ≤ tx := by omega
    have hmin : Nat.min tx ty = ty := Nat.min_eq_right hyx
    have hp :
        y.take (ty + 1) = x.take (ty + 1) := by
      have := hPrefix
      simpa [tx, ty, hmin] using this.symm
    have hLocal :
        (M.machine.run ty (initialTMConfig M.machine y)).state =
          (M.machine.run ty (initialTMConfig M.machine x)).state := by
      exact run_state_local
        M.machine ty
        (initialTMConfig M.machine y)
        (initialTMConfig M.machine x)
        rfl
        (initialTape_window_of_prefix ty y x hp)
    have hHaltY :
        M.machine.halting
          (M.machine.run ty (initialTMConfig M.machine y)).state = true := by
      exact hTotal y
    have hHaltX :
        M.machine.halting
          (M.machine.run ty (initialTMConfig M.machine x)).state = true := by
      rw [← hLocal]
      exact hHaltY
    have hExtend :
        M.machine.run tx (initialTMConfig M.machine x) =
          M.machine.run ty (initialTMConfig M.machine x) := by
      exact MachineRunLemmas.run_to_larger_fuel_of_halt
        M.machine
        (initialTMConfig M.machine x)
        (M.machine.run ty (initialTMConfig M.machine x))
        hyx
        rfl
        hHaltX
    unfold terminalState
    change
      (M.machine.run tx (initialTMConfig M.machine x)).state =
        (M.machine.run ty (initialTMConfig M.machine y)).state
    rw [hExtend]
    exact hLocal.symm

/-- Shared cone size for two possibly different-length inputs. -/
def SharedReadConePrefix
    (M : PolyDTMCandidate)
    (x y : BitString) : Nat :=
  Nat.min (M.timeBound x.length) (M.timeBound y.length) + 1

theorem sharedReadCone_invisibility
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (hCone :
      x.take (SharedReadConePrefix M x y) =
        y.take (SharedReadConePrefix M x y)) :
    terminalState M x = terminalState M y := by
  exact terminalState_of_shared_min_cone M hTotal x y hCone

theorem readCone_acceptance_invisibility
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length = y.length)
    (hCone :
      x.take (ReadConePrefix M x) =
        y.take (ReadConePrefix M x)) :
    DeclaredAccepts M x ↔ DeclaredAccepts M y := by
  have hs := readCone_invisibility M x y hLen hCone
  unfold DeclaredAccepts terminalState at *
  rw [hs]

#print axioms MCore.Real.PNPDiscovery.step_preserves_smaller_window
#print axioms MCore.Real.PNPDiscovery.run_state_local
#print axioms MCore.Real.PNPDiscovery.initialTape_window_of_prefix
#print axioms MCore.Real.PNPDiscovery.terminalState_of_prefix
#print axioms MCore.Real.PNPDiscovery.terminalState_of_shared_min_cone
#print axioms MCore.Real.PNPDiscovery.sharedReadCone_invisibility
#print axioms MCore.Real.PNPDiscovery.readCone_invisibility
#print axioms MCore.Real.PNPDiscovery.readCone_acceptance_invisibility

end PNPDiscovery
end Real
end MCore
