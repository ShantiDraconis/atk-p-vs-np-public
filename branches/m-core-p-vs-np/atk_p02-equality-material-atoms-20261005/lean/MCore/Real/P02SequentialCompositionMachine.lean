import MCore.Real.P02EqualityBranchMaterialFrontier
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02SequentialCompositionMachine

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Left-phase embedding into one finite state space. -/
def leftState
    {a b : Nat}
    (q : Fin (a + 1)) :
    Fin (a + b + 2) :=
  ⟨q.1, by omega⟩

/-- Right-phase embedding into the same finite state space. -/
def rightState
    {a b : Nat}
    (q : Fin (b + 1)) :
    Fin (a + b + 2) :=
  ⟨(a + 1) + q.1, by omega⟩

/-- Sequential composition skeleton.
Phase A runs first. When A is halted, one bridge step switches to B.initial
without changing the tape. Phase B then runs normally. -/
def sequentialTM
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    TM (Fin (a + b + 2)) (Option Bool) :=
  { initial := leftState A.initial
    blank := none
    transition := fun q symbol =>
      if hA : q.1 < a + 1 then
        let qa : Fin (a + 1) := ⟨q.1, hA⟩
        if A.halting qa then
          (rightState B.initial, symbol, .stay)
        else
          let stepA := A.transition qa symbol
          (leftState stepA.1, stepA.2.1, stepA.2.2)
      else
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        let stepB := B.transition qb symbol
        (rightState stepB.1, stepB.2.1, stepB.2.2)
    halting := fun q =>
      if hA : q.1 < a + 1 then
        false
      else
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        B.halting qb }

@[simp] theorem sequential_initial
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).initial = leftState A.initial :=
  rfl

@[simp] theorem sequential_blank
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).blank = none :=
  rfl

/-- Embed a phase-A configuration into the sequential machine. -/
def leftConfig
    {a b : Nat}
    (cfg : Configuration (Fin (a + 1)) (Option Bool)) :
    Configuration (Fin (a + b + 2)) (Option Bool) :=
  { state := leftState cfg.state
    tape := cfg.tape }

/-- Embed a phase-B configuration into the sequential machine. -/
def rightConfig
    {a b : Nat}
    (cfg : Configuration (Fin (b + 1)) (Option Bool)) :
    Configuration (Fin (a + b + 2)) (Option Bool) :=
  { state := rightState cfg.state
    tape := cfg.tape }

@[simp] theorem sequential_halting_left
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (q : Fin (a + 1)) :
    (sequentialTM A B).halting (leftState q) = false := by
  simp [sequentialTM, leftState]

@[simp] theorem sequential_halting_right
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (q : Fin (b + 1)) :
    (sequentialTM A B).halting (rightState q) = B.halting q := by
  have hnot : ¬ ((a + 1) + q.1 < a + 1) := by
    omega
  have hidx : (a + 1) + q.1 - (a + 1) = q.1 := by
    omega
  simp only [sequentialTM, rightState, hnot, dite_false]
  apply congrArg B.halting
  apply Fin.ext
  exact hidx

/-- While phase A is active, one sequential step is exactly one A-step,
embedded in the left state space. -/
theorem sequential_step_left_active
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (a + 1)) (Option Bool))
    (hactive : A.halting cfg.state = false) :
    (sequentialTM A B).step (leftConfig (b := b) cfg) =
      leftConfig (b := b) (A.step cfg) := by
  simp [TM.step, sequentialTM, leftConfig, leftState, hactive]

/-- Once in phase B, one sequential step is exactly one B-step,
embedded in the right state space. -/
theorem sequential_step_right
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).step (rightConfig (a := a) cfg) =
      rightConfig (a := a) (B.step cfg) := by
  have hnot : ¬ ((a + 1) + cfg.state.1 < a + 1) := by
    omega
  have hidx : (a + 1) + cfg.state.1 - (a + 1) = cfg.state.1 := by
    omega
  simp only [TM.step, sequentialTM, rightConfig, rightState, hnot, dite_false]
  have hstate :
      (⟨(a + 1) + cfg.state.1 - (a + 1), by omega⟩ : Fin (b + 1)) =
        cfg.state := by
    apply Fin.ext
    exact hidx
  simp [hstate]

/-- The bridge is physical: when A is halted, one step enters B.initial and
preserves the entire tape exactly. -/
theorem sequential_bridge_step
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (a + 1)) (Option Bool))
    (hhalt : A.halting cfg.state = true) :
    (sequentialTM A B).step (leftConfig (b := b) cfg) =
      rightConfig (a := a)
        { state := B.initial
          tape := cfg.tape } := by
  simp [TM.step, sequentialTM, leftConfig, rightConfig, leftState, rightState,
    hhalt, Tape.write, Tape.move]

/-- Remaining simulation theorem: phase A must be simulated until its halting
configuration, then the bridge theorem above and phase-B simulation compose.
This is now the only machine-level leaf for sequential composition. -/
def SEQUENTIAL_RUN_SIMULATION_OPEN_MATH : Prop :=
  ∀ {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (a + 1)) (Option Bool))
    (fuel : Nat),
    (sequentialTM A B).run fuel (leftConfig (b := b) cfg) =
      leftConfig (b := b) (A.run fuel cfg) ∨
    ∃ k : Nat, k ≤ fuel ∧
      A.halting (A.run k cfg).state = true

#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_initial
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_blank
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_left
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_right
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_step_left_active
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_step_right
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_bridge_step

end P02SequentialCompositionMachine
end Real
end MCore
