import MCore.Real.P01CheckedVerifierDeterminism

namespace MCore
namespace Real
namespace P01RawDeadEnd

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- In the deterministic checked verifier, reaching an active configuration
with no successors makes the next run frontier empty. Hence HaltsWithin holds
vacuously one step later. This covers fail-closed dead states that are not
explicitly labelled rejecting. -/
theorem haltsWithin_succ_of_reaches_dead
    (n : Nat)
    (start dead : CheckedVerifierConfig)
    (hmem :
      dead ∈ checkedVerifierMachine.runBranches n [start])
    (hactive : ¬ Halted checkedVerifierMachine dead)
    (hdead : checkedVerifierMachine.successors dead = []) :
    checkedVerifierMachine.HaltsWithin (n + 1) start := by
  have heq :
      checkedVerifierMachine.runBranches n [start] = [dead] :=
    runBranches_eq_singleton_of_mem n start dead hmem
  rw [haltsWithin_iff_halted]
  intro z hz
  rw [show n + 1 = n + 1 by rfl, runBranches_add, heq] at hz
  rw [runBranches_singleton_active checkedVerifierMachine 0 dead hactive] at hz
  simp [hdead, NTM.runBranches] at hz

/-- The same dead-end argument shows there is no accepting branch at the next
fuel. -/
theorem not_acceptsWithin_succ_of_reaches_dead
    (n : Nat)
    (start dead : CheckedVerifierConfig)
    (hmem :
      dead ∈ checkedVerifierMachine.runBranches n [start])
    (hactive : ¬ Halted checkedVerifierMachine dead)
    (hdead : checkedVerifierMachine.successors dead = []) :
    ¬ checkedVerifierMachine.AcceptsWithin (n + 1) start := by
  intro hacc
  rcases hacc with ⟨z, hz, hzacc⟩
  have heq :
      checkedVerifierMachine.runBranches n [start] = [dead] :=
    runBranches_eq_singleton_of_mem n start dead hmem
  rw [show n + 1 = n + 1 by rfl, runBranches_add, heq] at hz
  rw [runBranches_singleton_active checkedVerifierMachine 0 dead hactive] at hz
  simp [hdead, NTM.runBranches] at hz


/-- Once a run is known to have halted by fuel n, absence of an accepting
configuration at n persists at every larger fuel. -/
theorem not_acceptsWithin_mono_after_halt
    (n m : Nat)
    (start : CheckedVerifierConfig)
    (hnm : n ≤ m)
    (hhalt : checkedVerifierMachine.HaltsWithin n start)
    (hnot : ¬ checkedVerifierMachine.AcceptsWithin n start) :
    ¬ checkedVerifierMachine.AcceptsWithin m start := by
  intro hacc
  rcases hacc with ⟨z, hz, hzacc⟩
  have hzhalt : Halted checkedVerifierMachine z :=
    halted_of_accepting checkedVerifierMachine z hzacc
  have hzsmall :=
    mem_of_haltsWithin checkedVerifierMachine n m start z
      hhalt hz hzhalt
  exact hnot ⟨z, hzsmall, hzacc⟩

#print axioms MCore.Real.P01RawDeadEnd.haltsWithin_succ_of_reaches_dead
#print axioms MCore.Real.P01RawDeadEnd.not_acceptsWithin_succ_of_reaches_dead

end P01RawDeadEnd
end Real
end MCore
