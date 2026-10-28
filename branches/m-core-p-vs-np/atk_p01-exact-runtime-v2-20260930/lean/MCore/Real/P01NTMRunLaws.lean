import MCore.Real.Model

namespace MCore
namespace Real
namespace P01NTMRunLaws

/-!
# Global run laws for `NTM.runBranches`

Machine-generic lemmas.  Every previous `runBranches` lemma in the repository
was specialised to one concrete machine (witness guess, deterministic
embedding).  The integration of parser → witness guess → verifier into one
NTM needs these laws for an arbitrary machine.

No axioms beyond the Lean core are introduced; nothing here mentions SAT.
-/

variable {S Sym : Type} (M : NTM S Sym)

/-- A configuration is halted when it is accepting or rejecting. -/
def Halted (c : Configuration S Sym) : Prop :=
  (M.accepting c.state || M.rejecting c.state) = true

theorem runBranches_zero (xs : List (Configuration S Sym)) :
    M.runBranches 0 xs = xs := rfl

theorem runBranches_succ (n : Nat) (xs : List (Configuration S Sym)) :
    M.runBranches (n + 1) xs =
      M.runBranches n
        (xs.filter (fun c => M.accepting c.state || M.rejecting c.state) ++
          (xs.filter (fun c => !(M.accepting c.state || M.rejecting c.state))).flatMap
            M.successors) := by
  rfl

/-- G1: running `a` then `b` steps is running `a + b` steps. -/
theorem runBranches_add (a b : Nat) (xs : List (Configuration S Sym)) :
    M.runBranches (a + b) xs = M.runBranches b (M.runBranches a xs) := by
  induction a generalizing xs with
  | zero => simp [NTM.runBranches]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega, runBranches_succ, runBranches_succ]
      exact ih _

theorem runBranches_nil (n : Nat) :
    M.runBranches n ([] : List (Configuration S Sym)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [NTM.runBranches] using ih

/-- G2: `runBranches` distributes over append, up to membership. -/
theorem mem_runBranches_append (n : Nat) (xs ys : List (Configuration S Sym))
    (z : Configuration S Sym) :
    z ∈ M.runBranches n (xs ++ ys) ↔
      z ∈ M.runBranches n xs ∨ z ∈ M.runBranches n ys := by
  induction n generalizing xs ys with
  | zero => simp [NTM.runBranches]
  | succ n ih =>
      simp only [NTM.runBranches, List.filter_append, List.flatMap_append]
      rw [ih]
      simp only [ih]
      simpa [or_assoc, or_left_comm, or_comm]

/-- G3: membership in a list run is membership in some singleton run. -/
theorem mem_runBranches_iff (n : Nat) (xs : List (Configuration S Sym))
    (z : Configuration S Sym) :
    z ∈ M.runBranches n xs ↔ ∃ x ∈ xs, z ∈ M.runBranches n [x] := by
  induction xs with
  | nil => simp [runBranches_nil]
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, mem_runBranches_append, ih]
      constructor
      · rintro (h | ⟨y, hy, hz⟩)
        · exact ⟨x, by simp, h⟩
        · exact ⟨y, by simp [hy], hz⟩
      · rintro ⟨y, hy, hz⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl hz
        · exact Or.inr ⟨y, hy, hz⟩

/-- G4: a halted configuration is a fixed point of `runBranches`. -/
theorem runBranches_singleton_halted (n : Nat) (c : Configuration S Sym)
    (h : Halted M c) : M.runBranches n [c] = [c] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold Halted at h
      have h' : (!M.accepting c.state && !M.rejecting c.state) = false := by
        cases ha : M.accepting c.state <;> cases hr : M.rejecting c.state <;> simp_all
      simp [NTM.runBranches, List.filter_cons, h, h', ih]

/-- G5: an active configuration takes exactly one step. -/
theorem runBranches_singleton_active (n : Nat) (c : Configuration S Sym)
    (h : ¬ Halted M c) :
    M.runBranches (n + 1) [c] = M.runBranches n (M.successors c) := by
  unfold Halted at h
  have hf : (M.accepting c.state || M.rejecting c.state) = false := by
    cases hb : (M.accepting c.state || M.rejecting c.state) <;> simp_all
  have h' : (!M.accepting c.state && !M.rejecting c.state) = true := by
    cases ha : M.accepting c.state <;> cases hr : M.rejecting c.state <;> simp_all
  simp [NTM.runBranches, List.filter_cons, hf, h']

/-- A list of halted configurations is fixed by `runBranches`. -/
theorem runBranches_all_halted (n : Nat) (xs : List (Configuration S Sym))
    (h : ∀ x ∈ xs, Halted M x) : M.runBranches n xs = xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hfilt :
          xs.filter (fun c => M.accepting c.state || M.rejecting c.state) = xs := by
        apply List.filter_eq_self.2
        intro x hx
        exact h x hx
      have hact :
          xs.filter (fun c => !M.accepting c.state && !M.rejecting c.state) = [] := by
        apply List.filter_eq_nil_iff.2
        intro x hx
        have := h x hx
        unfold Halted at this
        cases ha : M.accepting x.state <;> cases hr : M.rejecting x.state <;> simp_all
      simp [NTM.runBranches, hfilt, hact, ih]

theorem halted_of_accepting (c : Configuration S Sym)
    (h : M.accepting c.state = true) : Halted M c := by
  simp [Halted, h]

theorem haltsWithin_iff_halted (n : Nat) (c : Configuration S Sym) :
    M.HaltsWithin n c ↔ ∀ z ∈ M.runBranches n [c], Halted M z := by
  unfold NTM.HaltsWithin Halted
  constructor
  · intro h z hz
    rcases h z hz with h | h <;> simp [h]
  · intro h z hz
    have := h z hz
    cases ha : M.accepting z.state <;> cases hr : M.rejecting z.state <;> simp_all

/-- One step forward: a successor of a reached active configuration is reached
one step later. -/
theorem mem_runBranches_succ_of_successor (n : Nat) (xs : List (Configuration S Sym))
    (c d : Configuration S Sym) (hc : c ∈ M.runBranches n xs) (hact : ¬ Halted M c)
    (hd : d ∈ M.successors c) : d ∈ M.runBranches (n + 1) xs := by
  rw [runBranches_add M n 1, mem_runBranches_iff]
  refine ⟨c, hc, ?_⟩
  rw [show (1 : Nat) = 0 + 1 from rfl, runBranches_singleton_active M 0 c hact]
  exact hd

/-- Reachability composes: reach `c` in `a` steps, then `z` from `c` in `b`. -/
theorem mem_runBranches_trans (a b : Nat) (xs : List (Configuration S Sym))
    (c z : Configuration S Sym) (hc : c ∈ M.runBranches a xs)
    (hz : z ∈ M.runBranches b [c]) : z ∈ M.runBranches (a + b) xs := by
  rw [runBranches_add, mem_runBranches_iff]
  exact ⟨c, hc, hz⟩

/-- Persistence: a reached halted configuration stays reached. -/
theorem mem_runBranches_persist (a k : Nat) (xs : List (Configuration S Sym))
    (c : Configuration S Sym) (hc : c ∈ M.runBranches a xs) (hh : Halted M c) :
    c ∈ M.runBranches (a + k) xs := by
  apply mem_runBranches_trans M a k xs c c hc
  rw [runBranches_singleton_halted M k c hh]
  simp

/-- Monotonicity of halting in the fuel. -/
theorem haltsWithin_mono (n k : Nat) (c : Configuration S Sym)
    (h : M.HaltsWithin n c) : M.HaltsWithin (n + k) c := by
  rw [haltsWithin_iff_halted] at h ⊢
  rw [runBranches_add, runBranches_all_halted M k _ h]
  exact h

theorem haltsWithin_mono_le (n m : Nat) (c : Configuration S Sym)
    (hnm : n ≤ m) (h : M.HaltsWithin n c) : M.HaltsWithin m c := by
  have := haltsWithin_mono M n (m - n) c h
  rwa [show n + (m - n) = m by omega] at this

/-- After halting, every halted configuration reached at any fuel was already
reached at the halting fuel. -/
theorem mem_of_haltsWithin (t n : Nat) (c z : Configuration S Sym)
    (hh : M.HaltsWithin t c) (hz : z ∈ M.runBranches n [c]) (hzh : Halted M z) :
    z ∈ M.runBranches t [c] := by
  rw [haltsWithin_iff_halted] at hh
  by_cases hnt : n ≤ t
  · have := mem_runBranches_persist M n (t - n) [c] z hz hzh
    rwa [show n + (t - n) = t by omega] at this
  · rw [show n = t + (n - t) by omega, runBranches_add,
      runBranches_all_halted M _ _ hh] at hz
    exact hz

/-! ## G6: simulation along a state map -/

/-- A state map `f : S → T` simulates `M` inside `N` when halting flags agree
and, on active configurations, `N`'s successors are exactly `M`'s successors
relabelled. -/
structure Simulation {T : Type} (N : NTM T Sym) (f : S → T) : Prop where
  accepting : ∀ s, N.accepting (f s) = M.accepting s
  rejecting : ∀ s, N.rejecting (f s) = M.rejecting s
  successors : ∀ c : Configuration S Sym, ¬ Halted M c →
    N.successors ⟨f c.state, c.tape⟩ =
      (M.successors c).map (fun d => ⟨f d.state, d.tape⟩)

def liftConfig {T : Type} (f : S → T) (c : Configuration S Sym) :
    Configuration T Sym := ⟨f c.state, c.tape⟩

theorem filter_map_lift {T : Type} (f : S → T)
    (p : Configuration T Sym → Bool) (q : Configuration S Sym → Bool)
    (hpq : ∀ c, p (liftConfig f c) = q c) (xs : List (Configuration S Sym)) :
    (xs.map (liftConfig f)).filter p = (xs.filter q).map (liftConfig f) := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
      simp only [List.map_cons, List.filter_cons, hpq]
      cases q c <;> simp [ih]

theorem flatMap_map_lift {T : Type} (N : NTM T Sym) (f : S → T)
    (ys : List (Configuration S Sym))
    (h : ∀ c ∈ ys, N.successors (liftConfig f c) =
      (M.successors c).map (liftConfig f)) :
    (ys.map (liftConfig f)).flatMap N.successors =
      (ys.flatMap M.successors).map (liftConfig f) := by
  induction ys with
  | nil => rfl
  | cons c ys ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [h c (by simp), ih (fun d hd => h d (by simp [hd]))]

theorem runBranches_map {T : Type} (N : NTM T Sym) (f : S → T)
    (hsim : Simulation M N f) (n : Nat) (xs : List (Configuration S Sym)) :
    N.runBranches n (xs.map (liftConfig f)) =
      (M.runBranches n xs).map (liftConfig f) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      rw [runBranches_succ, runBranches_succ M, ← ih, List.map_append]
      congr 1
      rw [filter_map_lift f _ (fun c => M.accepting c.state || M.rejecting c.state)
            (fun c => by simp [liftConfig, hsim.accepting, hsim.rejecting]),
          filter_map_lift f _ (fun c => !(M.accepting c.state || M.rejecting c.state))
            (fun c => by simp [liftConfig, hsim.accepting, hsim.rejecting]),
          flatMap_map_lift M N f]
      intro c hc
      have hact : ¬ Halted M c := by
        have := (List.mem_filter.1 hc).2
        unfold Halted
        intro h; simp [h] at this
      exact hsim.successors c hact

theorem mem_runBranches_map {T : Type} (N : NTM T Sym) (f : S → T)
    (hsim : Simulation M N f) (n : Nat) (c : Configuration S Sym)
    (z : Configuration T Sym) :
    z ∈ N.runBranches n [liftConfig f c] ↔
      ∃ d ∈ M.runBranches n [c], z = liftConfig f d := by
  have := runBranches_map M N f hsim n [c]
  simp only [List.map_cons, List.map_nil] at this
  rw [this, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, rfl⟩

#print axioms runBranches_add
#print axioms mem_runBranches_iff
#print axioms mem_of_haltsWithin
#print axioms runBranches_map

end P01NTMRunLaws
end Real
end MCore
