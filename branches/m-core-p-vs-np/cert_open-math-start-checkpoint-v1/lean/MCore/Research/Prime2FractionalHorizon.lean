import MCore.P012.P012PrimeArithmetic
import MCore.Research.Prime2ConservativeTransfer

namespace MCore
namespace Research
namespace Prime2

open MCore.P012

structure PrimeQuotient where
  numerator : Nat
  denominator : Nat
  numerator_prime : PrimeNat numerator
  denominator_prime : PrimeNat denominator
  coprime : Nat.gcd numerator denominator = 1

def PrimeQuotient.Pure (Q : PrimeQuotient) : Prop :=
  Q.numerator ≠ Q.denominator

theorem pure_prime_quotient_coprime
    (Q : PrimeQuotient)
    (_hPure : Q.Pure) :
    Nat.gcd Q.numerator Q.denominator = 1 :=
  Q.coprime

def PrimeDecimalHorizon (q : Nat) : Prop :=
  PrimeNat q ∧ q ≠ 2 ∧ q ≠ 5

instance instDecidablePrimeDecimalHorizon (q : Nat) :
    Decidable (PrimeDecimalHorizon q) := by
  unfold PrimeDecimalHorizon
  infer_instance

theorem prime_decimal_horizon_not_two
    {q : Nat} (h : PrimeDecimalHorizon q) :
    q ≠ 2 :=
  h.2.1

theorem prime_decimal_horizon_not_five
    {q : Nat} (h : PrimeDecimalHorizon q) :
    q ≠ 5 :=
  h.2.2

structure FractionalEvenShell where
  evenPart : Nat
  quotient : PrimeQuotient
  even : 2 ∣ evenPart

structure HorizonPrimeEvidence where
  quotient : PrimeQuotient
  pure : quotient.Pure
  decimalHorizon : PrimeDecimalHorizon quotient.denominator

theorem horizon_evidence_does_not_change_correctAt
    (I : ConservativePrime2Interpretation)
    (_H : HorizonPrimeEvidence)
    (M : Real.CanonicalFinalProof.PolyDTMCandidate)
    (x : Real.CanonicalFinalProof.BitString) :
    Prime2CorrectAt (I.mapCandidate M) (I.mapInput x) ↔
      CorrectAtStd M x :=
  I.correct_iff M x

#print axioms MCore.Research.Prime2.pure_prime_quotient_coprime
#print axioms MCore.Research.Prime2.horizon_evidence_does_not_change_correctAt

end Prime2
end Research
end MCore
