import MCore.Real.P01RawSourceSplit
import MCore.Real.P01RawGlobalBudgetLift
import MCore.Real.P01CheckedVerifierGlobalCoreV2

namespace MCore
namespace Real
namespace P01RawTotalizationMinCut

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01ExactVerifierGlobalBudget
open P01RawRecursiveBudget
open P01RawGlobalBudgetLift
open P01RawSourceSplit
open P01CheckedVerifierGlobalCoreV2

/-- Sole remaining raw-source obligation once canonical bounded evaluation has
been proved.

It says exactly what is needed for decoder failure at one uniform quartic
polynomial fuel. Canonical cubic execution is lifted to the same quartic fuel
by the already-proved post-halting stability law. No new machine, parser,
witness object, or mathematical hypothesis is introduced. -/
structure RawDecodeNoneFailClosed where
  halts :
    ∀ (bs w : BitString), w.length = bs.length →
      decodeCircuit bs = none →
      checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }
  rejects :
    ∀ (bs w : BitString), w.length = bs.length →
      decodeCircuit bs = none →
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }

/-- Canonical encodings plus fail-closed decoder failure cover EVERY raw source.
This constructs the exact global execution core needed by P01. -/
def RawDecodeNoneFailClosed.toGlobalCore
    (R : RawDecodeNoneFailClosed) :
    CheckedVerifierGlobalCore where
  timeBound := checkedVerifierRawTimeBound
  time_poly := checkedVerifierRawTimeBound_poly
  halts := by
    intro bs w hw
    rcases exact_encoding_or_decode_none bs with hcanon | hnone
    · rcases hcanon with ⟨phi, rfl⟩
      have hlen : varBound phi ≤ w.length := by
        rw [hw]
        exact varBound_le_encoded_length phi
      exact prepared_canonical_halts_within_raw_global w phi hlen
    · exact R.halts bs w hw hnone
  correct := by
    intro bs w hw
    rcases exact_encoding_or_decode_none bs with hcanon | hnone
    · rcases hcanon with ⟨phi, rfl⟩
      have hlen : varBound phi ≤ w.length := by
        rw [hw]
        exact varBound_le_encoded_length phi
      exact prepared_canonical_accepts_iff_raw_global w phi hlen
    · constructor
      · intro hacc
        exact False.elim ((R.rejects bs w hw hnone) hacc)
      · intro hverify
        exact False.elim (verifyBits_false_of_decode_none bs w hnone hverify)

/-- Exact mechanical closure theorem: proving raw decoder-failure rejection is
sufficient for the official P01ConstructionGap. -/
theorem p01ConstructionGap_of_rawDecodeNoneFailClosed
    (R : RawDecodeNoneFailClosed) :
    P01FinalCertificate.P01ConstructionGap :=
  p01ConstructionGap_of_core R.toGlobalCore

abbrev P01RawTotalizationGap : Prop :=
  Nonempty RawDecodeNoneFailClosed

theorem raw_totalization_gap_closes_p01
    (h : P01RawTotalizationGap) :
    P01FinalCertificate.P01ConstructionGap := by
  rcases h with ⟨R⟩
  exact p01ConstructionGap_of_rawDecodeNoneFailClosed R

#print axioms MCore.Real.P01RawTotalizationMinCut.RawDecodeNoneFailClosed.toGlobalCore
#print axioms MCore.Real.P01RawTotalizationMinCut.p01ConstructionGap_of_rawDecodeNoneFailClosed
#print axioms MCore.Real.P01RawTotalizationMinCut.raw_totalization_gap_closes_p01

end P01RawTotalizationMinCut
end Real
end MCore
