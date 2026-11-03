import MCore.Real.P01PreservingUnaryReaderCertificate

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine

def preservingUnaryTimeBound : TimeBound :=
  fun n => 64 * (n + 1) ^ 2

theorem preservingUnaryTimeBound_poly :
    PolynomialTimeBound preservingUnaryTimeBound := by
  exact ⟨64, 2, by intro n; exact Nat.le_refl _⟩

def PreservingUnaryHalts : Prop :=
  ∀ (witness : BitString) (i : Nat),
    i < witness.length →
    preservingUnaryReadMachine.HaltsWithin
      (preservingUnaryTimeBound (witness.length + (encodeNat i).length))
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape witness i }

def PreservingUnaryCorrect : Prop :=
  ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
    preservingReadAccepting
      (preservingUnaryReadMachine.run
        (preservingUnaryTimeBound (witness.length + (encodeNat i).length))
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape witness i }).state =
      witness.getD i false

def PreservingUnaryPreservesWitness : Prop :=
  ∀ (witness : BitString) (i : Nat) (hi : i < witness.length),
    ∃ left right : List (Option Bool),
      (preservingUnaryReadMachine.run
        (preservingUnaryTimeBound (witness.length + (encodeNat i).length))
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape witness i }).tape =
        { left := left ++ witness.map some
          head := none
          right := right }

def residuals_close_preserving_unary_reader
    (hhalts : PreservingUnaryHalts)
    (hcorrect : PreservingUnaryCorrect)
    (hpreserves : PreservingUnaryPreservesWitness) :
    PreservingUnaryReaderCertificate where
  machine := preservingUnaryReadMachine
  machine_eq := rfl
  accepting := preservingReadAccepting
  accepting_eq := rfl
  timeBound := preservingUnaryTimeBound
  time_poly := preservingUnaryTimeBound_poly
  halts := hhalts
  correct := hcorrect
  preservesWitness := hpreserves

#print axioms MCore.Real.P01PreservingUnaryReaderCertificate.preservingUnaryTimeBound_poly
#print axioms MCore.Real.P01PreservingUnaryReaderCertificate.residuals_close_preserving_unary_reader

end P01PreservingUnaryReaderCertificate
end Real
end MCore
