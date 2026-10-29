import MCore.Real.P01RawRecursiveBudget
import MCore.Real.P01ExactVerifierCanonicalRun

namespace MCore
namespace Real
namespace P01RawGlobalBudgetLift

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01ExactVerifierGlobalBudget
open P01ExactVerifierCanonicalRun
open P01RawRecursiveBudget
open P01CheckedVerifierCompositeNTM
open P01WitnessPreservingPrep

/-- Once a computation is known to have halted by fuel t, acceptance is stable
at every larger fuel m. -/
theorem acceptsWithin_iff_after_halt
    {S Sym : Type}
    (M : NTM S Sym)
    (t m : Nat)
    (c : Configuration S Sym)
    (htm : t ≤ m)
    (hh : M.HaltsWithin t c) :
    M.AcceptsWithin m c ↔ M.AcceptsWithin t c := by
  constructor
  · rintro ⟨z, hz, hacc⟩
    have hzh : Halted M z :=
      halted_of_accepting M z hacc
    exact ⟨z,
      mem_of_haltsWithin M t m c z hh hz hzh,
      hacc⟩
  · rintro ⟨z, hz, hacc⟩
    have hzh : Halted M z :=
      halted_of_accepting M z hacc
    have hp :=
      mem_runBranches_persist M t (m - t) [c] z hz hzh
    have heq : t + (m - t) = m := by omega
    exact ⟨z, by simpa [heq] using hp, hacc⟩

/-- Canonical-source halting lifts from the exact cubic certificate to the
single quartic raw-source budget. -/
theorem prepared_canonical_halts_within_raw_global
    (witness : BitString)
    (phi : CircuitK1.Circuit)
    (hlen : varBound phi ≤ witness.length) :
    checkedVerifierMachine.HaltsWithin
      (checkedVerifierRawTimeBound (encodeCircuit phi).length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (encodeCircuit phi) } := by
  have h :=
    prepared_canonical_halts_within_exact_global
      witness phi hlen
  exact haltsWithin_mono_le checkedVerifierMachine
    (checkedVerifierExactTimeBound (encodeCircuit phi).length)
    (checkedVerifierRawTimeBound (encodeCircuit phi).length)
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (encodeCircuit phi) }
    (exactTimeBound_le_rawTimeBound (encodeCircuit phi).length)
    h

/-- Canonical-source correctness is unchanged at the quartic raw-source fuel. -/
theorem prepared_canonical_accepts_iff_raw_global
    (witness : BitString)
    (phi : CircuitK1.Circuit)
    (hlen : varBound phi ≤ witness.length) :
    (checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound (encodeCircuit phi).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) } ↔
      P01GuessedWitnessRelation.VerifyBits
        (encodeCircuit phi) witness) := by
  let c : Configuration P01CheckedVerifierCompositeNTM.CheckedVerifierState
      (Option Bool) :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (encodeCircuit phi) }
  have hh :
      checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound (encodeCircuit phi).length) c := by
    simpa [c] using
      prepared_canonical_halts_within_exact_global witness phi hlen
  have hstable :=
    acceptsWithin_iff_after_halt
      checkedVerifierMachine
      (checkedVerifierExactTimeBound (encodeCircuit phi).length)
      (checkedVerifierRawTimeBound (encodeCircuit phi).length)
      c
      (exactTimeBound_le_rawTimeBound (encodeCircuit phi).length)
      hh
  exact hstable.trans
    (by simpa [c] using
      prepared_canonical_accepts_iff_exact_global witness phi hlen)

#print axioms MCore.Real.P01RawGlobalBudgetLift.acceptsWithin_iff_after_halt
#print axioms MCore.Real.P01RawGlobalBudgetLift.prepared_canonical_halts_within_raw_global
#print axioms MCore.Real.P01RawGlobalBudgetLift.prepared_canonical_accepts_iff_raw_global

end P01RawGlobalBudgetLift
end Real
end MCore
