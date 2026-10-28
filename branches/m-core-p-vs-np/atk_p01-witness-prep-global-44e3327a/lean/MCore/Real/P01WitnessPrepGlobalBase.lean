import MCore.Real.P01IntegratedNTMRequirements

namespace MCore
namespace Real
namespace P01WitnessPrepGlobalBase

open CanonicalFinalProof
open P01WitnessPreservingPrep

/-- Once every configuration in a branch list is terminal, additional NTM fuel
leaves that list unchanged. -/
theorem runBranches_terminal_fixed
    {State Symbol : Type}
    (machine : NTM State Symbol)
    (configs : List (Configuration State Symbol))
    (hterm : ∀ c ∈ configs,
      machine.accepting c.state = true ∨
        machine.rejecting c.state = true) :
    ∀ fuel, machine.runBranches fuel configs = configs := by
  intro fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      have hhalted :
          configs.filter (fun c =>
            machine.accepting c.state || machine.rejecting c.state) =
            configs := by
        apply List.filter_eq_self.2
        intro c hc
        rcases hterm c hc with ha | hr
        · simp [ha]
        · simp [hr]
      have hactive :
          configs.filter (fun c =>
            !(machine.accepting c.state || machine.rejecting c.state)) =
            [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        rcases hterm c hc with ha | hr
        · simp [ha]
        · simp [hr]
      rw [NTM.runBranches]
      rw [hhalted, hactive]
      simpa using ih

/-- Fuel composition for the repository NTM evaluator. -/
theorem runBranches_add
    {State Symbol : Type}
    (machine : NTM State Symbol)
    (m n : Nat)
    (configs : List (Configuration State Symbol)) :
    machine.runBranches (m + n) configs =
      machine.runBranches n (machine.runBranches m configs) := by
  induction m generalizing configs with
  | zero =>
      simp [NTM.runBranches]
  | succ m ih =>
      simp [Nat.succ_add, NTM.runBranches, ih]

/-- Halting within m steps is monotone in the fuel budget. -/
theorem ntm_haltsWithin_mono
    {State Symbol : Type}
    (machine : NTM State Symbol)
    (config : Configuration State Symbol)
    {m n : Nat}
    (hmn : m ≤ n)
    (hhalt : machine.HaltsWithin m config) :
    machine.HaltsWithin n config := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold NTM.HaltsWithin at hhalt ⊢
  rw [runBranches_add]
  rw [runBranches_terminal_fixed machine
    (machine.runBranches m [config]) hhalt k]
  exact hhalt

/-- Empty input reaches the accepting HALT state in one transition. -/
theorem witnessPrep_empty_runBranches_one :
    witnessPreservingPrep.runBranches 1
      [initialNTMConfig witnessPreservingPrep []] =
      [{ state := (11 : Fin 12), tape := inputTape [] }] := by
  rfl

theorem witnessPrep_empty_halts_one :
    witnessPreservingPrep.HaltsWithin 1
      (initialNTMConfig witnessPreservingPrep []) := by
  unfold NTM.HaltsWithin
  rw [witnessPrep_empty_runBranches_one]
  intro reached hmem
  simp only [List.mem_singleton] at hmem
  subst reached
  left
  rfl

/-- The certified cubic budget is large enough for the empty-input branch. -/
theorem witnessPrep_empty_halts :
    witnessPreservingPrep.HaltsWithin
      (witnessPrepTimeBound 0)
      (initialNTMConfig witnessPreservingPrep []) := by
  apply ntm_haltsWithin_mono witnessPreservingPrep
    (initialNTMConfig witnessPreservingPrep [])
    (m := 1)
  · change 1 ≤ 64
    decide
  · exact witnessPrep_empty_halts_one

/-- After the full certified budget, the empty input has exactly the canonical
empty prepared layout. -/
theorem witnessPrep_empty_runBranches :
    witnessPreservingPrep.runBranches (witnessPrepTimeBound 0)
      [initialNTMConfig witnessPreservingPrep []] =
      [{ state := (11 : Fin 12), tape := inputTape [] }] := by
  have hbound : witnessPrepTimeBound 0 = 1 + 63 := by
    rfl
  rw [hbound, runBranches_add, witnessPrep_empty_runBranches_one]
  apply runBranches_terminal_fixed
  intro c hc
  simp only [List.mem_singleton] at hc
  subst c
  left
  rfl

theorem witnessPrep_empty_layout
    (reached : Configuration (Fin 12) (Option Bool))
    (hmem : reached ∈
      witnessPreservingPrep.runBranches (witnessPrepTimeBound 0)
        [initialNTMConfig witnessPreservingPrep []]) :
    ∃ witness : BitString,
      reached.tape = preparedTape witness [] := by
  rw [witnessPrep_empty_runBranches] at hmem
  simp only [List.mem_singleton] at hmem
  subst reached
  exact ⟨[], rfl⟩


/-- A one-bit source is fully processed and rewound in exactly eight steps.
Both nondeterministic branches are preserved explicitly. -/
theorem witnessPrep_singleton_runBranches_eight
    (b : Bool) :
    witnessPreservingPrep.runBranches 8
      [initialNTMConfig witnessPreservingPrep [b]] =
      [ { state := (11 : Fin 12), tape := preparedTape [false] [b] },
        { state := (11 : Fin 12), tape := preparedTape [true] [b] } ] := by
  cases b <;> rfl

theorem witnessPrep_singleton_halts_eight
    (b : Bool) :
    witnessPreservingPrep.HaltsWithin 8
      (initialNTMConfig witnessPreservingPrep [b]) := by
  unfold NTM.HaltsWithin
  rw [witnessPrep_singleton_runBranches_eight]
  intro reached hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with h | h
  · subst reached
    left
    rfl
  · rcases h with h | h
    · subst reached
      left
      rfl
    · simp at h

theorem witnessPrep_singleton_layout_eight
    (b : Bool)
    (reached : Configuration (Fin 12) (Option Bool))
    (hmem : reached ∈
      witnessPreservingPrep.runBranches 8
        [initialNTMConfig witnessPreservingPrep [b]]) :
    ∃ witness : BitString,
      reached.tape = preparedTape witness [b] := by
  rw [witnessPrep_singleton_runBranches_eight] at hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with h | h
  · subst reached
    exact ⟨[false], rfl⟩
  · rcases h with h | h
    · subst reached
      exact ⟨[true], rfl⟩
    · simp at h

#print axioms MCore.Real.P01WitnessPrepGlobalBase.runBranches_terminal_fixed
#print axioms MCore.Real.P01WitnessPrepGlobalBase.ntm_haltsWithin_mono
#print axioms MCore.Real.P01WitnessPrepGlobalBase.witnessPrep_empty_halts
#print axioms MCore.Real.P01WitnessPrepGlobalBase.witnessPrep_empty_layout

end P01WitnessPrepGlobalBase
end Real
end MCore
