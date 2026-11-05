import Mathlib
import MCore.Real.P01PolynomialBudgetAlgebra
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P01PolynomialBudgetAlgebra
open P02UniversalFailureAlgebra

structure PolynomialResourceLaw where
  time : TimeBound
  space : TimeBound
  time_degree : ∃ k, DegreeBound time k
  space_degree : ∃ k, DegreeBound space k

theorem resourceLaw_time_poly
    (R : PolynomialResourceLaw) :
    PolynomialTimeBound R.time := by
  rcases R.time_degree with ⟨k, hk⟩
  exact degreeBound_implies_polynomial hk

theorem resourceLaw_space_poly
    (R : PolynomialResourceLaw) :
    PolynomialTimeBound R.space := by
  rcases R.space_degree with ⟨k, hk⟩
  exact degreeBound_implies_polynomial hk

structure HaltingMonotonicity where
  bound : TimeBound
  monotone : Monotone bound

structure TotalCandidateAsymptoticLaw where
  candidate : PolyDTMCandidate
  total : DeclaredClockTotal candidate
  polynomial : PolynomialTimeBound candidate.timeBound

end MCore.Real.OpenMathCore
