import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierDeterminism
import MCore.Real.P01MaterialGlobalBudget
import MCore.Real.P01GuessedWitnessRelation
import MCore.Real.P01ExactBoundedBinary

namespace MCore
namespace Real
namespace P01RawVerifierMaterialCore

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierGlobalBudget
open P01MaterialGlobalBudget
open P01GuessedWitnessRelation
open P01ExactBoundedBinary

/-- Exact raw-machine obligation after all local evaluator constructors and
global polynomial accounting have been separated from finite-state packaging.
This structure contains no endpoint proposition and no relabelling assumption. -/
structure RawVerifierMaterialCore : Prop where
  halts :
    ∀ (bs w : BitString), w.length = bs.length →
      checkedVerifierMachine.HaltsWithin
        (terminalVerifierTimeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }
  correct :
    ∀ (bs w : BitString), w.length = bs.length →
      (checkedVerifierMachine.AcceptsWithin
          (terminalVerifierTimeBound bs.length)
          { state := checkedVerifierMachine.initial,
            tape := preparedTape w bs } ↔
        VerifyBits bs w)

/-- Semantic split used by the terminal raw verifier proof. -/
theorem verifyBits_split
    (bs w : BitString) :
    VerifyBits bs w ↔
      ∃ phi : CircuitK1.Circuit,
        CanonicalCircuitBits.decodeCircuit bs = some phi ∧
        CircuitK1.IsCNF phi ∧
        CircuitK1.evalCircuit (fun i => w.getD i false) phi = true := by
  rfl

/-- Failure of the canonical decoder rules out the verifier relation outright. -/
theorem verifyBits_false_of_decode_none
    (bs w : BitString)
    (h : CanonicalCircuitBits.decodeCircuit bs = none) :
    ¬ VerifyBits bs w := by
  intro hv
  rcases hv with ⟨phi, hdec, _⟩
  rw [h] at hdec
  contradiction

#print axioms MCore.Real.P01RawVerifierMaterialCore.verifyBits_split
#print axioms MCore.Real.P01RawVerifierMaterialCore.verifyBits_false_of_decode_none

end P01RawVerifierMaterialCore
end Real
end MCore
