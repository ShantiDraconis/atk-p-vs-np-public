import MCore.Real.P01NTMPhaseSeq
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01NTMSeqRun

/-!
# Global semantics of sequential NTM composition

`P01NTMPhaseSeq.seq A B` previously had only one-step laws.  This module lifts
them to the global `runBranches` level:

* `seq_haltsWithin`: if `A` halts within `tA` and `B` halts within `tB` from
  every handoff of an accepting `A`-branch, `seq A B` halts within
  `tA + 1 + tB`;
* `seq_acceptsWithin_iff`: under the same hypotheses, `seq A B` accepts within
  `tA + 1 + tB` iff some accepting `A`-branch reached within `tA` hands off a
  tape from which `B` accepts within `tB`.

These are exactly the laws needed to compose parser → witness guess →
verifier into one machine.
-/

open P01NTMPhaseSeq P01NTMRunLaws

variable {SA SB Sym : Type} (A : NTM SA Sym) (B : NTM SB Sym)

/-- The configuration handed to `B` when an `A`-branch accepts. -/
def handoff (_A : NTM SA Sym) (B : NTM SB Sym) (d : Configuration SA Sym) :
    Configuration SB Sym :=
  ⟨B.initial, d.tape⟩

abbrev L (_A : NTM SA Sym) (_B : NTM SB Sym) (c : Configuration SA Sym) :
    Configuration (Sum SA SB) Sym :=
  liftConfig Sum.inl c

abbrev R (_A : NTM SA Sym) (_B : NTM SB Sym) (c : Configuration SB Sym) :
    Configuration (Sum SA SB) Sym :=
  liftConfig Sum.inr c

theorem seq_simulation_right (hblank : A.blank = B.blank) :
    Simulation B (seq A B) Sum.inr where
  accepting := fun _ => rfl
  rejecting := fun _ => rfl
  successors := fun c _ => seq_successors_right A B hblank c

theorem halted_R (b : Configuration SB Sym) :
    Halted (seq A B) (R A B b) ↔ Halted B b := Iff.rfl

theorem seq_haltsWithin_R_iff (hblank : A.blank = B.blank) (n : Nat)
    (b : Configuration SB Sym) :
    (seq A B).HaltsWithin n (R A B b) ↔ B.HaltsWithin n b := by
  rw [haltsWithin_iff_halted, haltsWithin_iff_halted]
  constructor
  · intro h z hz
    exact (halted_R A B z).1
      (h _ ((mem_runBranches_map B (seq A B) Sum.inr
        (seq_simulation_right A B hblank) n b _).2 ⟨z, hz, rfl⟩))
  · intro h z hz
    rcases (mem_runBranches_map B (seq A B) Sum.inr
      (seq_simulation_right A B hblank) n b z).1 hz with ⟨d, hd, rfl⟩
    exact (halted_R A B d).2 (h d hd)

/-- A rejecting `A`-branch is a halted (rejecting) `seq`-branch. -/
theorem halted_L_of_rejecting (c : Configuration SA Sym)
    (hrej : A.rejecting c.state = true) : Halted (seq A B) (L A B c) := by
  simp [Halted, L, liftConfig, seq, hrej]

/-- An accepting, non-rejecting `A`-branch hands off in one stationary step. -/
theorem seq_run_handoff (n : Nat) (c : Configuration SA Sym)
    (hacc : A.accepting c.state = true) (hrej : A.rejecting c.state = false) :
    (seq A B).runBranches (n + 1) [L A B c] =
      (seq A B).runBranches n [R A B (handoff A B c)] := by
  have hnot : ¬ Halted (seq A B) (L A B c) := by
    simp [Halted, L, liftConfig, seq, hrej]
  rw [runBranches_singleton_active _ n _ hnot]
  have := seq_successors_handoff A B c hacc
  simp only [L, liftConfig] at this ⊢
  rw [this]
  rfl

/-- An active `A`-branch steps exactly as in `A`. -/
theorem seq_run_active (n : Nat) (c : Configuration SA Sym)
    (hacc : A.accepting c.state = false) (hrej : A.rejecting c.state = false) :
    (seq A B).runBranches (n + 1) [L A B c] =
      (seq A B).runBranches n ((A.successors c).map (L A B)) := by
  have hnot : ¬ Halted (seq A B) (L A B c) := by
    simp [Halted, L, liftConfig, seq, hrej]
  rw [runBranches_singleton_active _ n _ hnot]
  have := seq_successors_left_active A B c hacc hrej
  simp only [L, liftConfig] at this ⊢
  rw [this]
  rfl

theorem mem_R_run_iff (hblank : A.blank = B.blank) (n : Nat)
    (b : Configuration SB Sym) (z : Configuration (Sum SA SB) Sym) :
    z ∈ (seq A B).runBranches n [R A B b] ↔
      ∃ b' ∈ B.runBranches n [b], z = R A B b' :=
  mem_runBranches_map B (seq A B) Sum.inr (seq_simulation_right A B hblank) n b z

theorem A_halted_iff (c : Configuration SA Sym) :
    Halted A c ↔ (A.accepting c.state = true ∨ A.rejecting c.state = true) := by
  unfold Halted
  cases A.accepting c.state <;> cases A.rejecting c.state <;> simp

/-! ## Halting -/

theorem seq_haltsWithin
    (hblank : A.blank = B.blank)
    (hdisj : ∀ q, A.accepting q = true → A.rejecting q = false)
    (tB : Nat) :
    ∀ (tA : Nat) (c : Configuration SA Sym),
      A.HaltsWithin tA c →
      (∀ d ∈ A.runBranches tA [c], A.accepting d.state = true →
        B.HaltsWithin tB (handoff A B d)) →
      (seq A B).HaltsWithin (tA + 1 + tB) (L A B c) := by
  intro tA
  induction tA with
  | zero =>
      intro c hA hB
      have hc : Halted A c := by
        rw [haltsWithin_iff_halted] at hA
        exact hA c (by simp [NTM.runBranches])
      rcases (A_halted_iff A c).1 hc with hacc | hrej
      · have hrej := hdisj _ hacc
        have hBc := hB c (by simp [NTM.runBranches]) hacc
        rw [haltsWithin_iff_halted]
        intro z hz
        rw [show 0 + 1 + tB = tB + 1 by omega, seq_run_handoff A B tB c hacc hrej] at hz
        rcases (mem_R_run_iff A B hblank tB _ z).1 hz with ⟨b, hb, rfl⟩
        exact (haltsWithin_iff_halted B tB _).1 hBc b hb
      · rw [haltsWithin_iff_halted]
        intro z hz
        rw [runBranches_singleton_halted _ _ _ (halted_L_of_rejecting A B c hrej)] at hz
        simp at hz
        subst hz
        exact halted_L_of_rejecting A B c hrej
  | succ tA ih =>
      intro c hA hB
      by_cases hc : Halted A c
      · -- `c` is already halted: reduce to fuel zero, then use monotonicity.
        have hA0 : A.HaltsWithin 0 c := by
          rw [haltsWithin_iff_halted]; intro z hz
          simp [NTM.runBranches] at hz; subst hz; exact hc
        have hB0 : ∀ d ∈ A.runBranches 0 [c], A.accepting d.state = true →
            B.HaltsWithin tB (handoff A B d) := by
          intro d hd hacc
          simp [NTM.runBranches] at hd; subst hd
          exact hB d (by rw [runBranches_singleton_halted _ _ _ hc]; simp) hacc
        -- the zero case of the statement, reproved inline
        have base : (seq A B).HaltsWithin (0 + 1 + tB) (L A B c) := by
          rcases (A_halted_iff A c).1 hc with hacc | hrej
          · have hrej := hdisj _ hacc
            have hBc := hB0 c (by simp [NTM.runBranches]) hacc
            rw [haltsWithin_iff_halted]
            intro z hz
            rw [show 0 + 1 + tB = tB + 1 by omega, seq_run_handoff A B tB c hacc hrej] at hz
            rcases (mem_R_run_iff A B hblank tB _ z).1 hz with ⟨b, hb, rfl⟩
            exact (haltsWithin_iff_halted B tB _).1 hBc b hb
          · rw [haltsWithin_iff_halted]
            intro z hz
            rw [runBranches_singleton_halted _ _ _ (halted_L_of_rejecting A B c hrej)] at hz
            simp at hz; subst hz
            exact halted_L_of_rejecting A B c hrej
        exact haltsWithin_mono_le _ _ _ _ (by omega) base
      · have hacc : A.accepting c.state = false := by
          cases h : A.accepting c.state
          · rfl
          · exact absurd ((A_halted_iff A c).2 (Or.inl h)) hc
        have hrej : A.rejecting c.state = false := by
          cases h : A.rejecting c.state
          · rfl
          · exact absurd ((A_halted_iff A c).2 (Or.inr h)) hc
        rw [haltsWithin_iff_halted]
        intro z hz
        rw [show tA + 1 + 1 + tB = (tA + 1 + tB) + 1 by omega,
          seq_run_active A B _ c hacc hrej, mem_runBranches_iff] at hz
        rcases hz with ⟨x, hx, hz⟩
        rcases List.mem_map.1 hx with ⟨c', hc', rfl⟩
        have hstep : ∀ w, w ∈ A.runBranches tA [c'] → w ∈ A.runBranches (tA + 1) [c] := by
          intro w hw
          rw [runBranches_singleton_active A tA c hc, mem_runBranches_iff]
          exact ⟨c', hc', hw⟩
        have hA' : A.HaltsWithin tA c' := by
          rw [haltsWithin_iff_halted] at hA ⊢
          exact fun w hw => hA w (hstep w hw)
        have hB' : ∀ d ∈ A.runBranches tA [c'], A.accepting d.state = true →
            B.HaltsWithin tB (handoff A B d) :=
          fun d hd hacc => hB d (hstep d hd) hacc
        exact (haltsWithin_iff_halted _ _ _).1 (ih c' hA' hB') z hz

/-! ## Acceptance -/

/-- Every accepting `seq`-branch comes from an accepting `A`-branch whose
handoff is accepted by `B`. -/
theorem seq_accept_forward
    (hblank : A.blank = B.blank)
    (hdisj : ∀ q, A.accepting q = true → A.rejecting q = false) :
    ∀ (n : Nat) (c : Configuration SA Sym) (z : Configuration (Sum SA SB) Sym),
      z ∈ (seq A B).runBranches n [L A B c] →
      (seq A B).accepting z.state = true →
      ∃ m, ∃ d ∈ A.runBranches m [c], A.accepting d.state = true ∧
        ∃ k, ∃ b ∈ B.runBranches k [handoff A B d], B.accepting b.state = true := by
  intro n
  induction n with
  | zero =>
      intro c z hz hacc
      simp [NTM.runBranches] at hz; subst hz
      simp [L, liftConfig, seq] at hacc
  | succ n ih =>
      intro c z hz hzacc
      cases hrej : A.rejecting c.state
      · cases hacc : A.accepting c.state
        · rw [seq_run_active A B n c hacc hrej, mem_runBranches_iff] at hz
          rcases hz with ⟨x, hx, hz⟩
          rcases List.mem_map.1 hx with ⟨c', hc', rfl⟩
          rcases ih c' z hz hzacc with ⟨m, d, hd, hdacc, k, b, hb, hbacc⟩
          have hcact : ¬ Halted A c := by
            rw [A_halted_iff]; simp [hacc, hrej]
          refine ⟨m + 1, d, ?_, hdacc, k, b, hb, hbacc⟩
          rw [runBranches_singleton_active A m c hcact, mem_runBranches_iff]
          exact ⟨c', hc', hd⟩
        · rw [seq_run_handoff A B n c hacc hrej] at hz
          rcases (mem_R_run_iff A B hblank n _ z).1 hz with ⟨b, hb, rfl⟩
          exact ⟨0, c, by simp [NTM.runBranches], hacc, n, b, hb, hzacc⟩
      · rw [runBranches_singleton_halted _ _ _ (halted_L_of_rejecting A B c hrej)] at hz
        simp at hz; subst hz
        simp [L, liftConfig, seq] at hzacc

/-- Conversely, an accepting `A`-branch at time `m` followed by an accepting
`B`-branch at time `k` is an accepting `seq`-branch at time `m + 1 + k`. -/
theorem seq_accept_backward
    (hblank : A.blank = B.blank)
    (hdisj : ∀ q, A.accepting q = true → A.rejecting q = false)
    (k : Nat) (b : Configuration SB Sym) (hbacc : B.accepting b.state = true) :
    ∀ (m : Nat) (c d : Configuration SA Sym),
      d ∈ A.runBranches m [c] → A.accepting d.state = true →
      b ∈ B.runBranches k [handoff A B d] →
      R A B b ∈ (seq A B).runBranches (m + 1 + k) [L A B c] := by
  have hRh : Halted (seq A B) (R A B b) := by
    simp [Halted, R, liftConfig, seq, hbacc]
  have base : ∀ c : Configuration SA Sym, A.accepting c.state = true →
      b ∈ B.runBranches k [handoff A B c] →
      R A B b ∈ (seq A B).runBranches (0 + 1 + k) [L A B c] := by
    intro c hacc hb
    rw [show 0 + 1 + k = k + 1 by omega, seq_run_handoff A B k c hacc (hdisj _ hacc)]
    exact (mem_R_run_iff A B hblank k _ _).2 ⟨b, hb, rfl⟩
  intro m
  induction m with
  | zero =>
      intro c d hd hdacc hb
      simp [NTM.runBranches] at hd; subst hd
      exact base d hdacc hb
  | succ m ih =>
      intro c d hd hdacc hb
      by_cases hc : Halted A c
      · rw [runBranches_singleton_halted _ _ _ hc] at hd
        simp at hd; subst hd
        have := mem_runBranches_persist _ (0 + 1 + k) (m + 1) _ _ (base d hdacc hb) hRh
        rwa [show 0 + 1 + k + (m + 1) = m + 1 + 1 + k by omega] at this
      · have hacc : A.accepting c.state = false := by
          cases h : A.accepting c.state
          · rfl
          · exact absurd ((A_halted_iff A c).2 (Or.inl h)) hc
        have hrej : A.rejecting c.state = false := by
          cases h : A.rejecting c.state
          · rfl
          · exact absurd ((A_halted_iff A c).2 (Or.inr h)) hc
        rw [runBranches_singleton_active A m c hc, mem_runBranches_iff] at hd
        rcases hd with ⟨c', hc', hd⟩
        rw [show m + 1 + 1 + k = (m + 1 + k) + 1 by omega,
          seq_run_active A B _ c hacc hrej, mem_runBranches_iff]
        exact ⟨L A B c', List.mem_map.2 ⟨c', hc', rfl⟩, ih c' d hd hdacc hb⟩

/-- Global acceptance law for `seq`, at the exact composed fuel. -/
theorem seq_acceptsWithin_iff
    (hblank : A.blank = B.blank)
    (hdisj : ∀ q, A.accepting q = true → A.rejecting q = false)
    (tA tB : Nat) (c : Configuration SA Sym)
    (hA : A.HaltsWithin tA c)
    (hB : ∀ d ∈ A.runBranches tA [c], A.accepting d.state = true →
      B.HaltsWithin tB (handoff A B d)) :
    (seq A B).AcceptsWithin (tA + 1 + tB) (L A B c) ↔
      ∃ d ∈ A.runBranches tA [c], A.accepting d.state = true ∧
        B.AcceptsWithin tB (handoff A B d) := by
  constructor
  · rintro ⟨z, hz, hzacc⟩
    rcases seq_accept_forward A B hblank hdisj _ c z hz hzacc with
      ⟨m, d, hd, hdacc, k, b, hb, hbacc⟩
    have hdA : d ∈ A.runBranches tA [c] :=
      mem_of_haltsWithin A tA m c d hA hd (halted_of_accepting A d hdacc)
    have hbB : b ∈ B.runBranches tB [handoff A B d] :=
      mem_of_haltsWithin B tB k _ b (hB d hdA hdacc) hb (halted_of_accepting B b hbacc)
    exact ⟨d, hdA, hdacc, b, hbB, hbacc⟩
  · rintro ⟨d, hd, hdacc, b, hb, hbacc⟩
    exact ⟨R A B b, seq_accept_backward A B hblank hdisj tB b hbacc tA c d hd hdacc hb,
      hbacc⟩

#print axioms seq_haltsWithin
#print axioms seq_acceptsWithin_iff

end P01NTMSeqRun
end Real
end MCore
