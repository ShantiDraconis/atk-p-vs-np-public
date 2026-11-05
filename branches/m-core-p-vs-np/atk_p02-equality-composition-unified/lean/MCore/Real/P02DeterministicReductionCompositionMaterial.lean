import MCore.Real.P02EqualityCompositionUnified
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02DeterministicReductionCompositionMaterial

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

def leftState
    {a b : Nat} (q : Fin (a + 1)) : Fin (a + b + 2) :=
  ⟨q.1, by omega⟩

def rightState
    {a b : Nat} (q : Fin (b + 1)) : Fin (a + b + 2) :=
  ⟨(a + 1) + q.1, by omega⟩

def leftConfig
    {a b : Nat}
    (cfg : Configuration (Fin (a + 1)) (Option Bool)) :
    Configuration (Fin (a + b + 2)) (Option Bool) :=
  { state := leftState cfg.state
    tape := cfg.tape }

def rightConfig
    {a b : Nat}
    (cfg : Configuration (Fin (b + 1)) (Option Bool)) :
    Configuration (Fin (a + b + 2)) (Option Bool) :=
  { state := rightState cfg.state
    tape := cfg.tape }

/-- Physical sequential machine used by the deterministic reduction composition:
run A; when A is halted, take one tape-preserving bridge step to B.initial;
then run B. -/
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
          let s := A.transition qa symbol
          (leftState s.1, s.2.1, s.2.2)
      else
        let qb : Fin (b + 1) := ⟨q.1 - (a + 1), by omega⟩
        let s := B.transition qb symbol
        (rightState s.1, s.2.1, s.2.2)
    halting := fun q =>
      if hA : q.1 < a + 1 then
        false
      else
        let qb : Fin (b + 1) := ⟨q.1 - (a + 1), by omega⟩
        B.halting qb }

@[simp] theorem sequential_initial
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).initial = leftState A.initial := rfl

@[simp] theorem sequential_blank
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).blank = none := rfl

@[simp] theorem halting_left
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (q : Fin (a + 1)) :
    (sequentialTM A B).halting (leftState q) = false := by
  simp [sequentialTM, leftState]

@[simp] theorem halting_right
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (q : Fin (b + 1)) :
    (sequentialTM A B).halting (rightState q) = B.halting q := by
  have hnot : ¬ ((a + 1) + q.1 < a + 1) := by omega
  have hidx : (a + 1) + q.1 - (a + 1) = q.1 := by omega
  simp only [sequentialTM, rightState, hnot, dite_false]
  apply congrArg B.halting
  apply Fin.ext
  exact hidx

theorem step_left_active
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (a + 1)) (Option Bool))
    (hblank : A.blank = none)
    (hactive : A.halting cfg.state = false) :
    (sequentialTM A B).step (leftConfig (b := b) cfg) =
      leftConfig (b := b) (A.step cfg) := by
  simp [TM.step, sequentialTM, leftConfig, leftState, hactive, hblank]

theorem bridge_step
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

theorem step_right
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (b + 1)) (Option Bool))
    (hblank : B.blank = none) :
    (sequentialTM A B).step (rightConfig (a := a) cfg) =
      rightConfig (a := a) (B.step cfg) := by
  have hnot : ¬ ((a + 1) + cfg.state.1 < a + 1) := by omega
  have hidx : (a + 1) + cfg.state.1 - (a + 1) = cfg.state.1 := by omega
  simp only [TM.step, sequentialTM, rightConfig, rightState, hnot, dite_false]
  have hstate :
      (⟨(a + 1) + cfg.state.1 - (a + 1), by omega⟩ : Fin (b + 1)) =
        cfg.state := by
    apply Fin.ext
    exact hidx
  simp [hstate, hblank]

/-- Exact phase-B simulation for arbitrary fuel. Once the composed machine
has crossed the bridge, every remaining step is exactly a B-step. -/
theorem run_right
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (b + 1)) (Option Bool))
    (hblank : B.blank = none)
    (fuel : Nat) :
    (sequentialTM A B).run fuel (rightConfig (a := a) cfg) =
      rightConfig (a := a) (B.run fuel cfg) := by
  induction fuel generalizing cfg with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [TM.run]
      change
        (if (sequentialTM A B).halting (rightState cfg.state) = true then
            rightConfig (a := a) cfg
          else
            (sequentialTM A B).run fuel
              ((sequentialTM A B).step (rightConfig (a := a) cfg))) =
          rightConfig (a := a) (B.run (fuel + 1) cfg)
      rw [halting_right]
      by_cases hhalt : B.halting cfg.state = true
      · simp only [hhalt, if_pos]
        rw [MachineRunLemmas.run_halted B cfg hhalt (fuel + 1)]
      · have hfalse : B.halting cfg.state = false := by
          cases h : B.halting cfg.state <;> simp_all
        simp only [hfalse, Bool.false_eq_true, if_false]
        rw [step_right A B cfg hblank]
        rw [ih]
        rw [TM.run]
        simp [hfalse]

#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.halting_left
#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.halting_right
#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.step_left_active
#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.bridge_step
#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.step_right
#print axioms MCore.Real.P02DeterministicReductionCompositionMaterial.run_right

end P02DeterministicReductionCompositionMaterial
end Real
end MCore
