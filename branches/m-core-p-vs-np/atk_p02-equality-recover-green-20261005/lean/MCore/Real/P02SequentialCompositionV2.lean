import MCore.Real.P02EqualityMaterialAtomsMaterial

namespace MCore
namespace Real
namespace P02SequentialCompositionV2

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

def leftState
    {a b : Nat}
    (q : Fin (a + 1)) :
    Fin (a + b + 2) :=
  ⟨q.1, by omega⟩

def rightState
    {a b : Nat}
    (q : Fin (b + 1)) :
    Fin (a + b + 2) :=
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
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        let s := B.transition qb symbol
        (rightState s.1, s.2.1, s.2.2)
    halting := fun q =>
      if hA : q.1 < a + 1 then
        false
      else
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        B.halting qb }

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

def COMPOSITION_RUN_OPEN_MATH : Prop := True

#print axioms MCore.Real.P02SequentialCompositionV2.halting_left
#print axioms MCore.Real.P02SequentialCompositionV2.halting_right
#print axioms MCore.Real.P02SequentialCompositionV2.step_left_active
#print axioms MCore.Real.P02SequentialCompositionV2.bridge_step

end P02SequentialCompositionV2
end Real
end MCore
