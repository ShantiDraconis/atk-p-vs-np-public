import MCore.Real.P02TerminalForcingG2
import MCore.Real.P02ClockBridgeMaterial
import MCore.Real.P02FiniteMachineDescription

namespace MCore
namespace Real
namespace P02G2BehavioralContract

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2
open P02ClockBridgeMaterial
open P02FiniteMachineDescription

/-- Finite polynomial clock certificate extracted from the existing
    PolynomialTimeBound proposition, without changing the candidate universe. -/
structure EncodedClock (M : PolyDTMCandidate) where
  coefficient : Nat
  exponent : Nat
  dominates :
    ∀ n, M.timeBound n ≤ polynomialMajorant coefficient exponent n

/-- The exact larger-clock candidate associated to a clock certificate. -/
def clockedCandidate
    (M : PolyDTMCandidate)
    (clock : EncodedClock M) :
    PolyDTMCandidate :=
  withMajorantClock M clock.coefficient clock.exponent

/-- Exact Boolean decision returned by the candidate at its clock horizon. -/
def clockedDecision
    (M : PolyDTMCandidate)
    (clock : EncodedClock M)
    (x : BitString) : Bool :=
  let M' := clockedCandidate M clock
  M'.accepting
    (M'.machine.run
      (M'.timeBound x.length)
      (initialTMConfig M'.machine x)).state

/-- Rejection at the certified polynomial horizon. -/
def RejectsAtMajorant
    (M : PolyDTMCandidate)
    (clock : EncodedClock M)
    (x : BitString) : Prop :=
  clockedDecision M clock x = false

/-- Existing polynomial certificate always yields an EncodedClock witness. -/
theorem encodedClock_exists
    (M : PolyDTMCandidate) :
    Nonempty (EncodedClock M) := by
  rcases M.time_poly with ⟨c, e, hLe⟩
  exact ⟨{ coefficient := c, exponent := e, dominates := hLe }⟩

/-- Correctness transports to the explicit polynomial majorant. -/
theorem correctAt_to_clockedCandidate
    (M : PolyDTMCandidate)
    (clock : EncodedClock M)
    (L : BitLanguage)
    (x : BitString)
    (h : M.CorrectAt L x) :
    (clockedCandidate M clock).CorrectAt L x := by
  exact correctAt_mono_clock
    M clock.coefficient clock.exponent clock.dominates L x h

/-- If the original candidate is correct, then the larger-clock decision
    equals the target language truth value. -/
theorem correctAt_clockedDecision_iff
    (M : PolyDTMCandidate)
    (clock : EncodedClock M)
    (L : BitLanguage)
    (x : BitString)
    (h : M.CorrectAt L x) :
    (clockedDecision M clock x = true ↔ L x) := by
  have hc := correctAt_to_clockedCandidate M clock L x h
  exact hc.2

/-- The precise self-reference law needed at the frontier:
    the SAT instance for M is satisfiable iff M rejects that very same instance
    at a certified polynomial majorant. -/
def SelfCodeFixedPointLaw
    (selfCode : PolyDTMCandidate → BitString) : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ clock : EncodedClock M,
      (P02UniversalFailureWitnessMaterial.CanonicalSAT (selfCode M) ↔
        RejectsAtMajorant M clock (selfCode M))

/-- The fixed-point law alone is already strong enough to force disagreement
    with CorrectAt on the same self-code. No search/wrapper is used here. -/
theorem fixedPointLaw_implies_disagreement
    (selfCode : PolyDTMCandidate → BitString)
    (hFix : SelfCodeFixedPointLaw selfCode) :
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt P02UniversalFailureWitnessMaterial.CanonicalSAT (selfCode M) := by
  intro M hCorrect
  rcases hFix M with ⟨clock, hFixM⟩
  have hDecision :=
    correctAt_clockedDecision_iff
      M clock P02UniversalFailureWitnessMaterial.CanonicalSAT (selfCode M) hCorrect
  cases hDecisionValue : clockedDecision M clock (selfCode M) <;>
    simp_all [RejectsAtMajorant]

/-- Behavioral contract replacing the opaque sorryAx by an explicit,
    typed material obligation. -/
structure G2BehavioralContract where
  selfCode : PolyDTMCandidate → BitString
  fixedPoint : SelfCodeFixedPointLaw selfCode

/-- Once a material inhabitant of G2BehavioralContract exists, the exact
    UniversalFailureWitness is constructible with no search layer. -/
def G2BehavioralContract.toUniversalFailureWitness
    (contract : G2BehavioralContract) :
    UniversalFailureWitness :=
  { counterexample := contract.selfCode
    fails :=
      fixedPointLaw_implies_disagreement
        contract.selfCode contract.fixedPoint }

/-- Exact equivalence at this specification layer: a contract is sufficient
    for the terminal payload. This direction intentionally makes no claim that
    every witness contains serialization/simulation/Cook-Levin data. -/
theorem behavioralContract_closes_G2
    (contract : G2BehavioralContract) :
    G2_TERMINAL := by
  refine ⟨contract.selfCode, ?_⟩
  exact
    (failureLaw_iff_correctAt contract.selfCode).mpr
      (fixedPointLaw_implies_disagreement
        contract.selfCode contract.fixedPoint)

#print axioms MCore.Real.P02G2BehavioralContract.encodedClock_exists
#print axioms MCore.Real.P02G2BehavioralContract.correctAt_to_clockedCandidate
#print axioms MCore.Real.P02G2BehavioralContract.correctAt_clockedDecision_iff
#print axioms MCore.Real.P02G2BehavioralContract.fixedPointLaw_implies_disagreement
#print axioms MCore.Real.P02G2BehavioralContract.G2BehavioralContract.toUniversalFailureWitness
#print axioms MCore.Real.P02G2BehavioralContract.behavioralContract_closes_G2

end P02G2BehavioralContract
end Real
end MCore
