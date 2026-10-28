import MCore.Real.FailProofAllGaps
import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02OperatorKernel

open CanonicalFinalProof
open FailProofAllGaps
open CanonicalSATBoundary
open CanonicalCircuitBits

/-- A counterexample operator assigns one concrete input to each deterministic
polynomial-time candidate. -/
abbrev CounterexampleOperator :=
  PolyDTMCandidate → BitString

/-- Soundness of a counterexample operator for a fixed language. -/
def CounterexampleSound
    (language : BitLanguage)
    (op : CounterexampleOperator) : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ¬ candidate.CorrectAt language (op candidate)

/-- The exact P02 producer shape, separated into operator plus soundness. -/
structure P02Producer (language : BitLanguage) where
  counterexample : CounterexampleOperator
  sound : CounterexampleSound language counterexample

def P02Producer.toFailureGenerator
    {language : BitLanguage}
    (P : P02Producer language) :
    FailureGenerator language :=
  { counterexample := P.counterexample
    fails := P.sound }

def P02Producer.ofFailureGenerator
    {language : BitLanguage}
    (G : FailureGenerator language) :
    P02Producer language :=
  { counterexample := G.counterexample
    sound := G.fails }

theorem p02Producer_iff_failureGenerator
    {language : BitLanguage} :
    Nonempty (P02Producer language) ↔
      Nonempty (FailureGenerator language) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toFailureGenerator⟩
  · rintro ⟨G⟩
    exact ⟨P02Producer.ofFailureGenerator G⟩

theorem p02Producer_iff_universalFailure
    {language : BitLanguage} :
    Nonempty (P02Producer language) ↔
      UniversalFailure language := by
  rw [p02Producer_iff_failureGenerator]
  exact failure_generator_iff_universal_failure

/-- Canonical SAT specialization: this is the sole P02 operator target. -/
abbrev CanonicalSATP02Producer :=
  P02Producer (SATBits circuitBitEncoding)

theorem canonicalSATProducer_iff_notInP :
    Nonempty CanonicalSATP02Producer ↔
      ¬ InP (SATBits circuitBitEncoding) := by
  rw [p02Producer_iff_universalFailure]
  exact universal_failure_iff_not_in_p

end P02OperatorKernel
end Real
end MCore
