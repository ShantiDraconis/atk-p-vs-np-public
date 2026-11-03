import MCore.P012.P012SignedThirdTransitions
import MCore.P012.P012PrimeArithmetic

namespace MCore
namespace P012

def PrimeNumerator (z : Int) : Prop :=
  PrimeNat z.natAbs

instance instDecidablePrimeNumerator (z : Int) :
    Decidable (PrimeNumerator z) := by
  unfold PrimeNumerator
  infer_instance

theorem primeNumerator_negTwo :
    PrimeNumerator (-2) := by decide

theorem primeNumerator_two :
    PrimeNumerator 2 := by decide

theorem primeNumerator_three :
    PrimeNumerator 3 := by decide

theorem not_primeNumerator_negOne :
    ¬ PrimeNumerator (-1) := by decide

theorem not_primeNumerator_zero :
    ¬ PrimeNumerator 0 := by decide

theorem not_primeNumerator_one :
    ¬ PrimeNumerator 1 := by decide

def PrimeThirdState (s : ThirdState) : Prop :=
  PrimeNumerator s.numerator

instance instDecidablePrimeThirdState (s : ThirdState) :
    Decidable (PrimeThirdState s) := by
  unfold PrimeThirdState
  infer_instance

theorem negTwoThirds_prime :
    PrimeThirdState negTwoThirds := by decide

theorem twoThirds_prime :
    PrimeThirdState twoThirds := by decide

theorem threeThirds_prime :
    PrimeThirdState threeThirds := by decide

theorem negOneThird_not_prime :
    ¬ PrimeThirdState negOneThird := by decide

theorem zeroThird_not_prime :
    ¬ PrimeThirdState zeroThird := by decide

theorem oneThird_not_prime :
    ¬ PrimeThirdState oneThird := by decide

def PrimeUnitThirdStep (a b : ThirdState) : Prop :=
  PrimeThirdState a ∧ PrimeThirdState b ∧ UnitThirdStep a b

instance instDecidablePrimeUnitThirdStep (a b : ThirdState) :
    Decidable (PrimeUnitThirdStep a b) := by
  unfold PrimeUnitThirdStep
  infer_instance

theorem no_prime_unit_step_neg2_neg1 :
    ¬ PrimeUnitThirdStep negTwoThirds negOneThird := by
  intro h
  exact negOneThird_not_prime h.2.1

theorem no_prime_unit_step_neg1_zero :
    ¬ PrimeUnitThirdStep negOneThird zeroThird := by
  intro h
  exact negOneThird_not_prime h.1

theorem no_prime_unit_step_zero_one :
    ¬ PrimeUnitThirdStep zeroThird oneThird := by
  intro h
  exact zeroThird_not_prime h.1

theorem no_prime_unit_step_one_two :
    ¬ PrimeUnitThirdStep oneThird twoThirds := by
  intro h
  exact oneThird_not_prime h.1

theorem prime_unit_step_two_three :
    PrimeUnitThirdStep twoThirds threeThirds := by
  exact ⟨twoThirds_prime, threeThirds_prime, step_two_three⟩

theorem fullCrossingPath_contains_nonprime_transition_states :
    ¬ (∀ s ∈ fullCrossingPath, PrimeThirdState s) := by
  intro h
  have hzero : PrimeThirdState zeroThird := h zeroThird (by decide)
  exact zeroThird_not_prime hzero

theorem canonical_unit_crossing_not_prime_only :
    ¬ (
      PrimeThirdState negTwoThirds ∧
      PrimeThirdState negOneThird ∧
      PrimeThirdState zeroThird ∧
      PrimeThirdState oneThird ∧
      PrimeThirdState twoThirds ∧
      PrimeThirdState threeThirds
    ) := by
  intro h
  exact zeroThird_not_prime h.2.2.1

#print axioms MCore.P012.fullCrossingPath_contains_nonprime_transition_states
#print axioms MCore.P012.canonical_unit_crossing_not_prime_only

end P012
end MCore
