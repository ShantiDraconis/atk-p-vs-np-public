import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01WitnessPrepGlobal

/-!
# Global semantics of `witnessPreservingPrep` and `Nonempty P01PrepPhase`

The Fin-12 witness-preserving preprocessor had only local successor lemmas.
This module proves its complete global behaviour:

* every branch from `inputTape bs` halts (accepting) within `prepCost bs.length`;
* the accepting branches are exactly the configurations
  `⟨11, preparedTape ws bs⟩` for all `ws` with `ws.length = bs.length`.

With the cubic budget `64 * (n + 1) ^ 3` this inhabits
`P01IntegratedAssembly.P01PrepPhase` with `layout bs w = preparedTape w bs`.
-/

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01NTMRunLaws
open P01IntegratedAssembly

/-! ## Generic deterministic / branching steps -/

section Generic

variable {S Sym : Type} (M : NTM S Sym)

theorem det_step (c : Configuration S Sym) (q' : S) (y : Sym) (d : Direction)
    (t : Configuration S Sym)
    (hact : ¬ Halted M c)
    (ht : M.transition c.state c.tape.head = [(q', y, d)])
    (htgt : (⟨q', Tape.move M.blank d (c.tape.write y)⟩ : Configuration S Sym) = t)
    (m : Nat) :
    M.runBranches (m + 1) [c] = M.runBranches m [t] := by
  rw [runBranches_singleton_active M m c hact]
  simp only [NTM.successors, ht, List.map_cons, List.map_nil, NTM.stepBranch]
  rw [← htgt]

theorem branch_step (c : Configuration S Sym) (q1 q2 : S) (y1 y2 : Sym)
    (d1 d2 : Direction) (t1 t2 : Configuration S Sym)
    (hact : ¬ Halted M c)
    (ht : M.transition c.state c.tape.head = [(q1, y1, d1), (q2, y2, d2)])
    (h1 : (⟨q1, Tape.move M.blank d1 (c.tape.write y1)⟩ : Configuration S Sym) = t1)
    (h2 : (⟨q2, Tape.move M.blank d2 (c.tape.write y2)⟩ : Configuration S Sym) = t2)
    (m : Nat) :
    M.runBranches (m + 1) [c] = M.runBranches m [t1, t2] := by
  rw [runBranches_singleton_active M m c hact]
  simp only [NTM.successors, ht, List.map_cons, List.map_nil, NTM.stepBranch]
  rw [← h1, ← h2]

end Generic

section Shuttles

variable {S : Type} (M : NTM S (Option Bool)) (hblank : M.blank = none)
include hblank

theorem shuttleLeft (q : S)
    (hq : ∀ x : Bool, M.transition q (some x) = [(q, some x, .left)])
    (hnh : ∀ t, ¬ Halted M (⟨q, t⟩ : Configuration S (Option Bool))) :
    ∀ (as : List Bool) (a : Bool) (L R : List (Option Bool)) (m : Nat),
      M.runBranches (as.length + 1 + m) [⟨q, ⟨as.map some ++ L, some a, R⟩⟩] =
        M.runBranches m
          [⟨q, ⟨L.tail, L.headD none, ((a :: as).reverse.map some) ++ R⟩⟩] := by
  intro as
  induction as with
  | nil =>
      intro a L R m
      rw [show ([] : List Bool).length + 1 + m = m + 1 by simp; omega]
      apply det_step M _ q (some a) .left _ (hnh _) (hq a)
      cases L <;> simp [Tape.move, Tape.write, hblank]
  | cons a' as ih =>
      intro a L R m
      rw [show (a' :: as).length + 1 + m = (as.length + 1 + m) + 1 by simp; omega]
      rw [det_step M _ q (some a) .left
        ⟨q, ⟨as.map some ++ L, some a', some a :: R⟩⟩ (hnh _) (hq a)
        (by simp [Tape.move, Tape.write]) _]
      rw [ih a' L (some a :: R) m]
      simp

theorem shuttleRight (q : S)
    (hq : ∀ x : Bool, M.transition q (some x) = [(q, some x, .right)])
    (hnh : ∀ t, ¬ Halted M (⟨q, t⟩ : Configuration S (Option Bool))) :
    ∀ (as : List Bool) (a : Bool) (L R : List (Option Bool)) (m : Nat),
      M.runBranches (as.length + 1 + m) [⟨q, ⟨L, some a, as.map some ++ R⟩⟩] =
        M.runBranches m
          [⟨q, ⟨((a :: as).reverse.map some) ++ L, R.headD none, R.tail⟩⟩] := by
  intro as
  induction as with
  | nil =>
      intro a L R m
      rw [show ([] : List Bool).length + 1 + m = m + 1 by simp; omega]
      apply det_step M _ q (some a) .right _ (hnh _) (hq a)
      cases R <;> simp [Tape.move, Tape.write, hblank]
  | cons a' as ih =>
      intro a L R m
      rw [show (a' :: as).length + 1 + m = (as.length + 1 + m) + 1 by simp; omega]
      rw [det_step M _ q (some a) .right
        ⟨q, ⟨some a :: L, some a', as.map some ++ R⟩⟩ (hnh _) (hq a)
        (by simp [Tape.move, Tape.write]) _]
      rw [ih a' (some a :: L) R m]
      simp

end Shuttles

/-! ## Facts about the concrete machine -/

abbrev P := witnessPreservingPrep

theorem not_halted (q : Fin 12) (hq : q ≠ 11) (t : Tape (Option Bool)) :
    ¬ Halted P (⟨q, t⟩ : Configuration (Fin 12) (Option Bool)) := by
  unfold Halted
  simp [P, witnessPreservingPrep]
  exact hq

theorem halted_11 (t : Tape (Option Bool)) :
    Halted P (⟨11, t⟩ : Configuration (Fin 12) (Option Bool)) := by
  simp [Halted, P, witnessPreservingPrep]

/-- The stored-bit dependent state quadruple of one cycle. -/
def sL1 : Bool → Fin 12 | false => 2 | true => 3
def sL2 : Bool → Fin 12 | false => 4 | true => 5
def sR1 : Bool → Fin 12 | false => 6 | true => 7
def sR2 : Bool → Fin 12 | false => 8 | true => 9

theorem t_dispatch1 (b : Bool) :
    P.transition 1 (some b) = [(sL1 b, none, .left)] := by cases b <;> rfl
theorem t_dispatch0 (b : Bool) :
    P.transition 0 (some b) = [(sL1 b, none, .left)] := by cases b <;> rfl
theorem t_L1_some (b x : Bool) :
    P.transition (sL1 b) (some x) = [(sL1 b, some x, .left)] := by
  cases b <;> cases x <;> rfl
theorem t_L1_none (b : Bool) :
    P.transition (sL1 b) none = [(sL2 b, none, .left)] := by cases b <;> rfl
theorem t_L2_some (b x : Bool) :
    P.transition (sL2 b) (some x) = [(sL2 b, some x, .left)] := by
  cases b <;> cases x <;> rfl
theorem t_L2_none (b : Bool) :
    P.transition (sL2 b) none =
      [(sR1 b, some false, .right), (sR1 b, some true, .right)] := by
  cases b <;> rfl
theorem t_R1_some (b x : Bool) :
    P.transition (sR1 b) (some x) = [(sR1 b, some x, .right)] := by
  cases b <;> cases x <;> rfl
theorem t_R1_none (b : Bool) :
    P.transition (sR1 b) none = [(sR2 b, none, .right)] := by cases b <;> rfl
theorem t_R2_some (b x : Bool) :
    P.transition (sR2 b) (some x) = [(sR2 b, some x, .right)] := by
  cases b <;> cases x <;> rfl
theorem t_R2_none (b : Bool) :
    P.transition (sR2 b) none = [(1, some b, .right)] := by cases b <;> rfl
theorem t_finish1 : P.transition 1 none = [(10, none, .left)] := rfl
theorem t_10_some (x : Bool) :
    P.transition 10 (some x) = [(10, some x, .left)] := by cases x <;> rfl
theorem t_10_none : P.transition 10 none = [(11, none, .right)] := rfl
theorem t_empty : P.transition 0 none = [(11, none, .stay)] := rfl

theorem nh (q : Fin 12) (hq : q ≠ 11 := by decide) (t : Tape (Option Bool)) :
    ¬ Halted P (⟨q, t⟩ : Configuration (Fin 12) (Option Bool)) :=
  not_halted q hq t

theorem nh_L1 (b : Bool) (t) : ¬ Halted P (⟨sL1 b, t⟩ : Configuration _ _) := by
  cases b <;> exact nh _ (by decide) t
theorem nh_L2 (b : Bool) (t) : ¬ Halted P (⟨sL2 b, t⟩ : Configuration _ _) := by
  cases b <;> exact nh _ (by decide) t
theorem nh_R1 (b : Bool) (t) : ¬ Halted P (⟨sR1 b, t⟩ : Configuration _ _) := by
  cases b <;> exact nh _ (by decide) t
theorem nh_R2 (b : Bool) (t) : ¬ Halted P (⟨sR2 b, t⟩ : Configuration _ _) := by
  cases b <;> exact nh _ (by decide) t

/-! ## One cycle -/

/-- Configuration at the start of a cycle, and at the end of the preparation. -/
def cycConfig (Dl W : List Bool) (R : List (Option Bool)) :
    Configuration (Fin 12) (Option Bool) :=
  ⟨1, ⟨Dl.map some ++ none :: W.map some, R.headD none, R.tail⟩⟩

/-- Right half of a cycle, after the witness bit `x` has been written.
`u :: us` is the witness block read right-to-left, `v :: vs` the processed
source block read right-to-left. -/
theorem cycle_right (b x u : Bool) (us : List Bool) (v : Bool) (vs : List Bool)
    (R : List (Option Bool)) (m : Nat) :
    P.runBranches (us.length + 1 + ((vs.length + 1 + (m + 1)) + 1))
        [⟨sR1 b, ⟨[some x], some u,
          us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩] =
      P.runBranches m
        [cycConfig (b :: (v :: vs).reverse) ((u :: us).reverse ++ [x]) R] := by
  rw [shuttleRight P rfl (sR1 b) (t_R1_some b) (nh_R1 b) us u [some x]
    (none :: (some v :: (vs.map some ++ none :: R))) _]
  simp only [List.headD_cons, List.tail_cons]
  rw [det_step P _ (sR2 b) none .right
    ⟨sR2 b, ⟨none :: (((u :: us).reverse.map some) ++ [some x]), some v,
      vs.map some ++ none :: R⟩⟩ (nh_R1 b _) (t_R1_none b)
    (by simp [Tape.move, Tape.write]) _]
  rw [shuttleRight P rfl (sR2 b) (t_R2_some b) (nh_R2 b) vs v _ (none :: R) _]
  simp only [List.headD_cons, List.tail_cons]
  rw [det_step P _ 1 (some b) .right
    (cycConfig (b :: (v :: vs).reverse) ((u :: us).reverse ++ [x]) R) (nh_R2 b _)
    (t_R2_none b) ?_ m]
  cases R <;> simp [Tape.move, Tape.write, cycConfig]

/-- One full cycle for the source bit `b`, with `i = Dl.length = W.length ≥ 1`. -/
theorem cycle (b : Bool) (Dl W : List Bool) (hD : Dl ≠ []) (hlen : Dl.length = W.length)
    (R : List (Option Bool)) (m : Nat) (z : Configuration (Fin 12) (Option Bool)) :
    z ∈ P.runBranches (4 * Dl.length + 5 + m)
        [⟨1, ⟨Dl.map some ++ none :: W.map some, some b, R⟩⟩] ↔
      ∃ x : Bool, z ∈ P.runBranches m [cycConfig (b :: Dl) (W ++ [x]) R] := by
  have hW : W ≠ [] := by
    intro h; subst h; exact hD (List.eq_nil_of_length_eq_zero hlen)
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, Dl = d :: ds := by
    cases Dl with
    | nil => exact absurd rfl hD
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨w, ws, rfl⟩ : ∃ w ws, W = w :: ws := by
    cases W with
    | nil => exact absurd rfl hW
    | cons w ws => exact ⟨w, ws, rfl⟩
  obtain ⟨u, us, hu⟩ : ∃ u us, (w :: ws).reverse = u :: us := by
    cases h : (w :: ws).reverse with
    | nil => simp at h
    | cons u us => exact ⟨u, us, rfl⟩
  obtain ⟨v, vs, hv⟩ : ∃ v vs, (d :: ds).reverse = v :: vs := by
    cases h : (d :: ds).reverse with
    | nil => simp at h
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hus : us.length = ws.length := by
    have := congrArg List.length hu; simp at this; omega
  have hvs : vs.length = ds.length := by
    have := congrArg List.length hv; simp at this; omega
  have hl : ds.length = ws.length := by simpa using hlen
  have hWr : (u :: us).reverse = w :: ws := by rw [← hu, List.reverse_reverse]
  have hDr : (v :: vs).reverse = d :: ds := by rw [← hv, List.reverse_reverse]
  have key : ∀ x : Bool,
      P.runBranches (us.length + 1 + ((vs.length + 1 + (m + 1)) + 1))
        [⟨sR1 b, ⟨[some x], some u,
          us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩] =
      P.runBranches m [cycConfig (b :: d :: ds) ((w :: ws) ++ [x]) R] := by
    intro x
    rw [cycle_right b x u us v vs R m, hWr, hDr]
  rw [show 4 * (d :: ds).length + 5 + m =
      ((ds.length + 1 + ((ws.length + 1 +
        ((us.length + 1 + ((vs.length + 1 + (m + 1)) + 1)) + 1)) + 1)) + 1) by
    simp; omega]
  -- dispatch: q1 reads b, blanks it, moves left
  rw [det_step P _ (sL1 b) none .left
    ⟨sL1 b, ⟨ds.map some ++ none :: (w :: ws).map some, some d,
      none :: R⟩⟩ (nh 1 (by decide) _) (t_dispatch1 b)
    (by simp [Tape.move, Tape.write]) _]
  -- shuttle left over processed source
  rw [shuttleLeft P rfl (sL1 b) (t_L1_some b) (nh_L1 b) ds d
    (none :: (w :: ws).map some) (none :: R) _]
  simp only [List.tail_cons, List.headD_cons]
  rw [hv]
  -- delimiter: sL1 none → sL2, move left
  rw [det_step P _ (sL2 b) none .left
    ⟨sL2 b, ⟨ws.map some, some w,
      none :: (((v :: vs).map some) ++ none :: R)⟩⟩ (nh_L1 b _) (t_L1_none b)
    (by simp [Tape.move, Tape.write]) _]
  -- shuttle left over the witness block onto the far-left blank
  have hsh := shuttleLeft P rfl (sL2 b) (t_L2_some b) (nh_L2 b) ws w []
    (none :: (((v :: vs).map some) ++ none :: R))
    ((us.length + 1 + ((vs.length + 1 + (m + 1)) + 1)) + 1)
  simp only [List.append_nil, List.tail_nil, List.headD_nil] at hsh
  rw [hsh]
  rw [hu]
  -- the single nondeterministic step
  rw [branch_step P _ (sR1 b) (sR1 b) (some false) (some true) .right .right
    ⟨sR1 b, ⟨[some false], some u,
      us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩
    ⟨sR1 b, ⟨[some true], some u,
      us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩
    (nh_L2 b _) (t_L2_none b)
    (by simp [Tape.move, Tape.write]) (by simp [Tape.move, Tape.write]) _]
  rw [show ([⟨sR1 b, ⟨[some false], some u,
        us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩,
      ⟨sR1 b, ⟨[some true], some u,
        us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩] :
        List (Configuration (Fin 12) (Option Bool))) =
      [⟨sR1 b, ⟨[some false], some u,
        us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩] ++
      [⟨sR1 b, ⟨[some true], some u,
        us.map some ++ none :: (some v :: (vs.map some ++ none :: R))⟩⟩] from rfl,
    mem_runBranches_append, key false, key true]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨x, h⟩
    cases x
    · exact Or.inl h
    · exact Or.inr h

/-! ## Finish, empty input, first cycle -/

theorem finish (Dl W : List Bool) (hD : Dl ≠ []) (m : Nat) :
    P.runBranches (Dl.length + 2 + m) [cycConfig Dl W []] =
      P.runBranches m [⟨11, preparedTape W Dl.reverse⟩] := by
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, Dl = d :: ds := by
    cases Dl with
    | nil => exact absurd rfl hD
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨v, vs, hv⟩ : ∃ v vs, (d :: ds).reverse = v :: vs := by
    cases h : (d :: ds).reverse with
    | nil => simp at h
    | cons v vs => exact ⟨v, vs, rfl⟩
  rw [show (d :: ds).length + 2 + m = (ds.length + 1 + (m + 1)) + 1 by simp; omega]
  rw [det_step P (cycConfig (d :: ds) W []) 10 none .left
    ⟨10, ⟨ds.map some ++ none :: W.map some, some d, [none]⟩⟩
    (nh 1 (by decide) _) t_finish1 (by simp [Tape.move, Tape.write, cycConfig]) _]
  rw [shuttleLeft P rfl 10 t_10_some (fun t => nh 10 (by decide) t) ds d
    (none :: W.map some) [none] _]
  simp only [List.tail_cons, List.headD_cons]
  rw [hv]
  apply det_step P _ 11 none .right _ (nh 10 (by decide) _) t_10_none
  simp [Tape.move, Tape.write, preparedTape]

theorem empty_run (m : Nat) :
    P.runBranches (1 + m) [initialNTMConfig P []] =
      [⟨11, preparedTape [] []⟩] := by
  rw [show 1 + m = m + 1 by omega]
  rw [det_step P (initialNTMConfig P []) 11 none .stay ⟨11, preparedTape [] []⟩ (nh 0 (by decide) _)
    t_empty (by simp [Tape.move, Tape.write, preparedTape, inputTape, initialNTMConfig]) m]
  exact runBranches_singleton_halted P m _ (halted_11 _)

theorem first_cycle (b : Bool) (rest : List Bool) (m : Nat)
    (z : Configuration (Fin 12) (Option Bool)) :
    z ∈ P.runBranches (5 + m) [initialNTMConfig P (b :: rest)] ↔
      ∃ x : Bool, z ∈ P.runBranches m [cycConfig [b] [x] (rest.map some)] := by
  have key : ∀ x : Bool,
      P.runBranches ((m + 1) + 1)
        [⟨sR1 b, ⟨[some x], none, none :: rest.map some⟩⟩] =
      P.runBranches m [cycConfig [b] [x] (rest.map some)] := by
    intro x
    rw [det_step P _ (sR2 b) none .right
      ⟨sR2 b, ⟨[none, some x], none, rest.map some⟩⟩ (nh_R1 b _) (t_R1_none b)
      (by simp [Tape.move, Tape.write]) _]
    apply det_step P _ 1 (some b) .right _ (nh_R2 b _) (t_R2_none b)
    cases rest <;> simp [Tape.move, Tape.write, cycConfig]
  rw [show 5 + m = ((((m + 1) + 1) + 1) + 1) + 1 by omega]
  rw [det_step P (initialNTMConfig P (b :: rest)) (sL1 b) none .left
    ⟨sL1 b, ⟨[], none, none :: rest.map some⟩⟩ (nh 0 (by decide) _) (t_dispatch0 b)
    (by cases rest <;> simp [Tape.move, Tape.write, initialNTMConfig, inputTape]) _]
  rw [det_step P _ (sL2 b) none .left
    ⟨sL2 b, ⟨[], none, none :: none :: rest.map some⟩⟩ (nh_L1 b _) (t_L1_none b)
    (by simp [Tape.move, Tape.write]) _]
  rw [branch_step P _ (sR1 b) (sR1 b) (some false) (some true) .right .right
    ⟨sR1 b, ⟨[some false], none, none :: rest.map some⟩⟩
    ⟨sR1 b, ⟨[some true], none, none :: rest.map some⟩⟩
    (nh_L2 b _) (t_L2_none b)
    (by simp [Tape.move, Tape.write]) (by simp [Tape.move, Tape.write]) _]
  rw [show ([⟨sR1 b, ⟨[some false], none, none :: rest.map some⟩⟩,
        ⟨sR1 b, ⟨[some true], none, none :: rest.map some⟩⟩] :
        List (Configuration (Fin 12) (Option Bool))) =
      [⟨sR1 b, ⟨[some false], none, none :: rest.map some⟩⟩] ++
      [⟨sR1 b, ⟨[some true], none, none :: rest.map some⟩⟩] from rfl,
    mem_runBranches_append, key false, key true]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨x, h⟩
    cases x
    · exact Or.inl h
    · exact Or.inr h

/-! ## Global run -/

/-- Exact cost from a cycle start with `i` processed cells and `k` remaining. -/
def cost : Nat → Nat → Nat
  | i, 0 => i + 2
  | i, k + 1 => 4 * i + 5 + cost (i + 1) k

theorem global_run (rest : List Bool) :
    ∀ (Dl W : List Bool), Dl ≠ [] → Dl.length = W.length →
    ∀ (m : Nat) (z : Configuration (Fin 12) (Option Bool)),
      z ∈ P.runBranches (cost Dl.length rest.length + m)
          [cycConfig Dl W (rest.map some)] ↔
        ∃ ws : List Bool, ws.length = rest.length ∧
          z = ⟨11, preparedTape (W ++ ws) (Dl.reverse ++ rest)⟩ := by
  induction rest with
  | nil =>
      intro Dl W hD _ m z
      rw [show cost Dl.length ([] : List Bool).length + m = Dl.length + 2 + m by
        simp [cost]]
      simp only [List.map_nil]
      rw [finish Dl W hD m, runBranches_singleton_halted P m _ (halted_11 _)]
      simp
  | cons c cs ih =>
      intro Dl W hD hlen m z
      have hcfg : cycConfig Dl W ((c :: cs).map some) =
          ⟨1, ⟨Dl.map some ++ none :: W.map some, some c, cs.map some⟩⟩ := by
        simp [cycConfig]
      rw [hcfg, show cost Dl.length (c :: cs).length + m =
          4 * Dl.length + 5 + (cost (Dl.length + 1) cs.length + m) by
        simp [cost]; omega]
      rw [cycle c Dl W hD hlen _ _ z]
      constructor
      · rintro ⟨x, hx⟩
        have hx' := (ih (c :: Dl) (W ++ [x]) (by simp) (by simp [hlen]) m z).1
          (by simpa using hx)
        rcases hx' with ⟨ws, hws, rfl⟩
        exact ⟨x :: ws, by simp [hws], by simp⟩
      · rintro ⟨ws, hws, rfl⟩
        cases ws with
        | nil => simp at hws
        | cons x ws' =>
            refine ⟨x, ?_⟩
            have := (ih (c :: Dl) (W ++ [x]) (by simp) (by simp [hlen]) m
              ⟨11, preparedTape (W ++ x :: ws') (Dl.reverse ++ c :: cs)⟩).2
              ⟨ws', by simpa using hws, by simp⟩
            simpa using this

def prepCost : Nat → Nat
  | 0 => 1
  | n + 1 => 5 + cost 1 n

/-- Complete branch semantics of the witness-preserving preprocessor. -/
theorem prep_run (bs : BitString) (m : Nat)
    (z : Configuration (Fin 12) (Option Bool)) :
    z ∈ P.runBranches (prepCost bs.length + m) [initialNTMConfig P bs] ↔
      ∃ ws : List Bool, ws.length = bs.length ∧ z = ⟨11, preparedTape ws bs⟩ := by
  cases bs with
  | nil =>
      rw [show prepCost ([] : BitString).length + m = 1 + m by simp [prepCost],
        empty_run]
      constructor
      · intro h; simp at h; exact ⟨[], rfl, h⟩
      · rintro ⟨ws, hws, rfl⟩
        cases ws with
        | nil => simp
        | cons _ _ => simp at hws
  | cons b rest =>
      rw [show prepCost (b :: rest).length + m = 5 + (cost 1 rest.length + m) by
        simp [prepCost]; omega, first_cycle]
      constructor
      · rintro ⟨x, hx⟩
        rcases (global_run rest [b] [x] (by simp) rfl m z).1 hx with ⟨ws, hws, rfl⟩
        exact ⟨x :: ws, by simp [hws], by simp⟩
      · rintro ⟨ws, hws, rfl⟩
        cases ws with
        | nil => simp at hws
        | cons x ws' =>
            refine ⟨x, (global_run rest [b] [x] (by simp) rfl m _).2
              ⟨ws', by simpa using hws, by simp⟩⟩

/-! ## Cost bounds -/

theorem cost_le (k : Nat) : ∀ i, cost i k ≤ (k + 1) * (4 * (i + k) + 5) + i + k + 2 := by
  induction k with
  | zero => intro i; simp [cost]
  | succ k ih =>
      intro i
      have h := ih (i + 1)
      have e : 4 * (i + 1 + k) + 5 = 4 * (i + (k + 1)) + 5 := by omega
      rw [e] at h
      simp only [cost]
      rw [Nat.succ_mul (k + 1)]
      generalize (k + 1) * (4 * (i + (k + 1)) + 5) = Y at *
      omega

theorem prepCost_le (n : Nat) : prepCost n ≤ witnessPrepTimeBound n := by
  unfold witnessPrepTimeBound
  cases n with
  | zero => simp [prepCost]
  | succ n =>
      simp only [prepCost]
      have h1 := cost_le n 1
      have h2 : (n + 1) * (4 * (1 + n) + 5) ≤ (n + 2) * (5 * (n + 2)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (n + 1 + 1) ^ 3 = (n + 2) * (n + 2) * (n + 2) := by
        simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      have h4 : (n + 2) * (n + 2) ≤ (n + 2) * (n + 2) * (n + 2) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h5 : n + 2 ≤ (n + 2) * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
      have h6 : (n + 2) * (5 * (n + 2)) = 5 * ((n + 2) * (n + 2)) := by
        rw [Nat.mul_left_comm]
      rw [h3]
      generalize (n + 1) * (4 * (1 + n) + 5) = A at *
      generalize (n + 2) * (5 * (n + 2)) = B at *
      generalize (n + 2) * (n + 2) * (n + 2) = C at *
      generalize (n + 2) * (n + 2) = D at *
      omega

/-! ## The prep phase object -/

theorem prep_run_T (bs : BitString) (z : Configuration (Fin 12) (Option Bool)) :
    z ∈ P.runBranches (witnessPrepTimeBound bs.length) [initialNTMConfig P bs] ↔
      ∃ ws : List Bool, ws.length = bs.length ∧ z = ⟨11, preparedTape ws bs⟩ := by
  have h := prepCost_le bs.length
  rw [show witnessPrepTimeBound bs.length =
      prepCost bs.length + (witnessPrepTimeBound bs.length - prepCost bs.length) by omega]
  exact prep_run bs _ z

/-- `P01PrepPhase` is inhabited by the certified Fin-12 witness-preserving
preprocessor, with handoff layout `preparedTape w bs`. -/
def prepPhase : P01PrepPhase where
  stateCount := 11
  machine := witnessPreservingPrep
  blank_none := rfl
  disjoint := fun _ _ => rfl
  timeBound := witnessPrepTimeBound
  time_poly := witnessPrepTimeBound_poly
  layout := fun bs w => preparedTape w bs
  halts := by
    intro bs
    rw [haltsWithin_iff_halted]
    intro z hz
    rcases (prep_run_T bs z).1 hz with ⟨ws, _, rfl⟩
    exact halted_11 _
  sound := by
    intro bs d hd _
    rcases (prep_run_T bs d).1 hd with ⟨ws, hws, rfl⟩
    exact ⟨ws, hws, rfl⟩
  complete := by
    intro bs w hw
    exact ⟨⟨11, preparedTape w bs⟩, (prep_run_T bs _).2 ⟨w, hw, rfl⟩, rfl, rfl⟩

theorem prepPhase_layout (bs w : BitString) :
    prepPhase.layout bs w = preparedTape w bs := rfl

-- 1. P01GapTolerantRead DENTRO do mesmo arquivo - sem import, proof-complete

def evalCursorStackEndTape (w : List Bool) (gap : Nat) (rem : List Bool) : List Bool :=
  w ++ List.replicate gap false ++ rem

def gapTolerantRead : Nat → List Bool → Option Bool
  | _, [] => none
  | 0, b :: _ => some b
  | n+1, _ :: bs => gapTolerantRead n bs

theorem gapTolerant_append_left (i : Nat) (l₁ l₂ : List Bool) (h : i < l₁.length) :
  gapTolerantRead i (l₁ ++ l₂) = gapTolerantRead i l₁ := by
  induction l₁ generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => rfl
    | succ n => simp; exact ih n (by simp at h ⊢; omega)

theorem gapTolerant_correct :
  ∀ i witness, i < witness.length →
    gapTolerantRead i witness = witness[i]? := by
  intro i w hi
  induction w generalizing i with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          rfl
      | succ n =>
          have hi' : n < bs.length := by
            simpa using hi
          simp only [gapTolerantRead]
          simpa using ih n hi'

theorem gapTolerant_correct_with_gap :
  ∀ i witness rem gap, i < witness.length →
    gapTolerantRead i (evalCursorStackEndTape witness gap rem) = witness[i]? := by
  intro i w rem gap hi
  unfold evalCursorStackEndTape
  have hleft :=
    gapTolerant_append_left i w (List.replicate gap false ++ rem) hi
  rw [show w ++ List.replicate gap false ++ rem =
      w ++ (List.replicate gap false ++ rem) by
      simp [List.append_assoc]]
  rw [hleft]
  exact gapTolerant_correct i w hi

def physicalEvalStep_input_gapTolerant (i : Nat) (tape : List Bool) : Bool :=
  (gapTolerantRead i tape).getD false

theorem input000_gap_complete :
  ∀ i w gap rem, i < w.length →
    physicalEvalStep_input_gapTolerant i (evalCursorStackEndTape w gap rem) =
      (w[i]?).getD false := by
  intro i w gap rem hi
  unfold physicalEvalStep_input_gapTolerant
  rw [gapTolerant_correct_with_gap i w rem gap hi]

#print axioms gapTolerant_correct
#print axioms gapTolerant_correct_with_gap
#print axioms input000_gap_complete

/-- With the prep phase inhabited, P01 reduces to a single verifier phase.

No verifier inhabitant is asserted here: the remaining obligation is exactly a
concrete `P01VerifierPhase prepPhase.layout`. -/
theorem p01_of_verifier (V : P01VerifierPhase prepPhase.layout) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_phases prepPhase V


#print axioms prep_run
#print axioms prepPhase
#print axioms p01_of_verifier

end P01WitnessPrepGlobal
end Real
end MCore
