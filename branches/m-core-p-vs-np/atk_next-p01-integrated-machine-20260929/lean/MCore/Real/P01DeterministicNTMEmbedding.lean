import MCore.Real.Model

namespace MCore
namespace Real
namespace P01DeterministicNTMEmbedding

/-- Embed a deterministic TM into the repository's NTM model by giving every
non-halting configuration exactly one successor.  A halted TM state is split
into accepting/rejecting according to the supplied terminal classifier. -/
def tmAsNTM
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) : NTM State Symbol where
  initial := M.initial
  blank := M.blank
  transition := fun q a =>
    if M.halting q then [] else [M.transition q a]
  accepting := fun q => M.halting q && accepting q
  rejecting := fun q => M.halting q && !accepting q

@[simp] theorem tmAsNTM_initial
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).initial = M.initial := rfl

@[simp] theorem tmAsNTM_blank
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).blank = M.blank := rfl

/-- On every non-halting state the embedded NTM has exactly the deterministic
TM step as its unique successor. -/
theorem tmAsNTM_successors_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).successors c = [M.step c] := by
  simp [tmAsNTM, NTM.successors, NTM.stepBranch, TM.step, h]

/-- A halted TM state is terminal in the embedded NTM. -/
theorem tmAsNTM_terminal_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h : M.halting q = true) :
    (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true := by
  cases ha : accepting q <;> simp [tmAsNTM, h, ha]

/-- Conversely, an NTM terminal state in the embedding is a halted TM state. -/
theorem tmAsNTM_terminal_implies_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h :
      (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) :
    M.halting q = true := by
  cases hm : M.halting q with
  | false =>
      rcases h with h | h <;> simp [tmAsNTM, hm] at h
  | true =>
      rfl


/-- One deterministic run step is reproduced by the singleton-branch NTM. -/
theorem runBranches_singleton_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).runBranches 1 [c] = [M.step c] := by
  have ha : (tmAsNTM M accepting).accepting c.state = false := by
    simp [tmAsNTM, h]
  have hr : (tmAsNTM M accepting).rejecting c.state = false := by
    simp [tmAsNTM, h]
  have hs := tmAsNTM_successors_of_not_halted M accepting c h
  simp [NTM.runBranches, ha, hr, hs]

/-- A halted TM configuration is already terminal for the embedded NTM. -/
theorem runBranches_singleton_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = true) :
    (tmAsNTM M accepting).runBranches 1 [c] = [c] := by
  have ht := tmAsNTM_terminal_of_halted M accepting c.state h
  rcases ht with ha | hr
  · simp [NTM.runBranches, ha]
  · simp [NTM.runBranches, hr]

/-- The embedded NTM classifies exactly the halted TM states as terminal. -/
theorem tmAsNTM_terminal_iff_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State) :
    ((tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) ↔
      M.halting q = true := by
  constructor
  · exact tmAsNTM_terminal_implies_halted M accepting q
  · exact tmAsNTM_terminal_of_halted M accepting q


/-- Once a deterministic state has halted, the embedded NTM keeps that single
configuration unchanged for any additional fuel. -/
theorem runBranches_halted_all
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (n : Nat)
    (c : Configuration State Symbol)
    (h : M.halting c.state = true) :
    (tmAsNTM M accepting).runBranches n [c] = [c] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have ht := tmAsNTM_terminal_of_halted M accepting c.state h
      rcases ht with ha | hr
      · simp [NTM.runBranches, ha, ih]
      · simp [NTM.runBranches, hr, ih]

/-- Full-run correspondence: the deterministic embedding has exactly one
reachable branch, namely the original TM run. -/
theorem runBranches_tmAsNTM_singleton
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (n : Nat)
    (c : Configuration State Symbol) :
    (tmAsNTM M accepting).runBranches n [c] = [M.run n c] := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      cases h : M.halting c.state with
      | false =>
          have ha : (tmAsNTM M accepting).accepting c.state = false := by
            simp [tmAsNTM, h]
          have hr : (tmAsNTM M accepting).rejecting c.state = false := by
            simp [tmAsNTM, h]
          have hs := tmAsNTM_successors_of_not_halted M accepting c h
          rw [TM.run]
          simp [h, NTM.runBranches, ha, hr, hs, ih]
      | true =>
          rw [TM.run]
          simp [h]
          exact runBranches_halted_all M accepting (n + 1) c h

/-- Deterministic halting is preserved exactly by the singleton-branch
embedding. -/
theorem tmHaltsWithin_iff_ntmHaltsWithin
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (n : Nat)
    (c : Configuration State Symbol) :
    M.HaltsWithin n c ↔
      (tmAsNTM M accepting).HaltsWithin n c := by
  unfold TM.HaltsWithin NTM.HaltsWithin
  rw [runBranches_tmAsNTM_singleton]
  simp only [List.mem_singleton]
  constructor
  · intro h reached hEq
    subst reached
    exact tmAsNTM_terminal_of_halted M accepting _ h
  · intro h
    exact tmAsNTM_terminal_implies_halted M accepting _
      (h (M.run n c) rfl)

/-- Under the halting certificate, NTM acceptance is exactly the deterministic
terminal classifier on the unique TM run. -/
theorem tmAsNTM_acceptsWithin_iff
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (n : Nat)
    (c : Configuration State Symbol)
    (hhalt : M.HaltsWithin n c) :
    (tmAsNTM M accepting).AcceptsWithin n c ↔
      accepting (M.run n c).state = true := by
  unfold NTM.AcceptsWithin
  rw [runBranches_tmAsNTM_singleton]
  constructor
  · rintro ⟨reached, hmem, hacc⟩
    simp only [List.mem_singleton] at hmem
    subst reached
    have hpair :
        M.halting (M.run n c).state = true ∧
          accepting (M.run n c).state = true := by
      simpa [tmAsNTM] using hacc
    exact hpair.2
  · intro hacc
    refine ⟨M.run n c, by simp, ?_⟩
    have hh : M.halting (M.run n c).state = true := hhalt
    simp [tmAsNTM, hh, hacc]

#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_successors_of_not_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_of_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_implies_halted

end P01DeterministicNTMEmbedding
end Real
end MCore
