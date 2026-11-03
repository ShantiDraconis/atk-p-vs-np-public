import MCore.P012.P012PrimeKernel

namespace MCore
namespace P012

def OddPrimeNumerator (z : Int) : Prop :=
  PrimeNumerator z ∧ z.natAbs ≠ 2

instance instDecidableOddPrimeNumerator (z : Int) :
    Decidable (OddPrimeNumerator z) := by
  unfold OddPrimeNumerator
  infer_instance

def OddPrimeThirdState (s : ThirdState) : Prop :=
  OddPrimeNumerator s.numerator

instance instDecidableOddPrimeThirdState (s : ThirdState) :
    Decidable (OddPrimeThirdState s) := by
  unfold OddPrimeThirdState
  infer_instance

theorem five_is_odd_prime_numerator :
    OddPrimeNumerator 5 := by decide

theorem negFive_is_odd_prime_numerator :
    OddPrimeNumerator (-5) := by decide

theorem two_not_odd_prime_numerator :
    ¬ OddPrimeNumerator 2 := by decide

def PureOddPrimeThirdState (s : ThirdState) : Prop :=
  OddPrimeThirdState s ∧ s.numerator.natAbs ≠ 3

instance instDecidablePureOddPrimeThirdState (s : ThirdState) :
    Decidable (PureOddPrimeThirdState s) := by
  unfold PureOddPrimeThirdState
  infer_instance

theorem negFive_pure :
    PureOddPrimeThirdState ⟨-5⟩ := by decide

theorem five_pure :
    PureOddPrimeThirdState ⟨5⟩ := by decide

theorem negThree_not_pure :
    ¬ PureOddPrimeThirdState ⟨-3⟩ := by decide

theorem three_not_pure :
    ¬ PureOddPrimeThirdState ⟨3⟩ := by decide

theorem central_odd_prime_gap_displacement :
    displacementNumerator ⟨-5⟩ ⟨5⟩ = 10 := by decide

theorem no_pure_odd_prime_canonical_crossing :
    ¬ (∀ s ∈ fullCrossingPath, PureOddPrimeThirdState s) := by
  intro h
  have hz := h zeroThird (by decide)
  exact zeroThird_not_prime hz.1.1

theorem operational_kernel_not_in_odd_prime_space :
    ¬ OddPrimeThirdState ⟨2⟩ := by decide

#print axioms MCore.P012.central_odd_prime_gap_displacement
#print axioms MCore.P012.no_pure_odd_prime_canonical_crossing
#print axioms MCore.P012.operational_kernel_not_in_odd_prime_space

end P012
end MCore
