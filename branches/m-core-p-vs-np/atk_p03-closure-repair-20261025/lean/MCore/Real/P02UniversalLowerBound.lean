import MCore.Real.P02FinalCompression

namespace MCore
namespace Real
namespace P02UniversalLowerBound

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel

abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- Candidate halts inside its own declared polynomial clock. -/
def HaltsAtDeclaredBound
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

/-- Candidate's declared acceptance proposition at the end of its clock. -/
def AcceptsAtDeclaredBound
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- Semantic disagreement with canonical SAT on one input. -/
def SemanticMismatch
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  ¬ (AcceptsAtDeclaredBound M x ↔ SATTarget x)

/-- Exact one-input lower-bound failure. -/
def FailureAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  ¬ M.CorrectAt SATTarget x

theorem correctAt_iff_halts_and_semantics
    (M : PolyDTMCandidate)
    (x : BitString) :
    M.CorrectAt SATTarget x ↔
      HaltsAtDeclaredBound M x ∧
      (AcceptsAtDeclaredBound M x ↔ SATTarget x) := by
  rfl

theorem failureAt_iff_nonhalting_or_mismatch
    (M : PolyDTMCandidate)
    (x : BitString) :
    FailureAt M x ↔
      ¬ HaltsAtDeclaredBound M x ∨ SemanticMismatch M x := by
  unfold FailureAt SemanticMismatch
  rw [correctAt_iff_halts_and_semantics]
  constructor
  · intro h
    by_cases hH : HaltsAtDeclaredBound M x
    · right
      intro hSem
      exact h ⟨hH, hSem⟩
    · exact Or.inl hH
  · intro h hBoth
    rcases h with hH | hSem
    · exact hH hBoth.1
    · exact hSem hBoth.2

/-- Mismatch can be witnessed in exactly one of the two Boolean directions. -/
theorem semanticMismatch_iff_wrong_yes_or_wrong_no
    (M : PolyDTMCandidate)
    (x : BitString) :
    SemanticMismatch M x ↔
      (AcceptsAtDeclaredBound M x ∧ ¬ SATTarget x) ∨
      (¬ AcceptsAtDeclaredBound M x ∧ SATTarget x) := by
  unfold SemanticMismatch
  constructor
  · intro h
    by_cases hA : AcceptsAtDeclaredBound M x
    · left
      refine ⟨hA, ?_⟩
      intro hSAT
      apply h
      constructor
      · intro _
        exact hSAT
      · intro _
        exact hA
    · right
      refine ⟨hA, ?_⟩
      apply Classical.byContradiction
      intro hNotSAT
      apply h
      constructor
      · intro hAcc
        exact False.elim (hA hAcc)
      · intro hSAT
        exact False.elim (hNotSAT hSAT)
  · intro h hEq
    rcases h with ⟨hA, hNotSAT⟩ | ⟨hNotA, hSAT⟩
    · exact hNotSAT (hEq.mp hA)
    · exact hNotA (hEq.mpr hSAT)

/-- Canonical universal lower bound, stated directly as a failure input for
every polynomial-time deterministic candidate. -/
def UniversalSATLowerBound : Prop :=
  ∀ M : PolyDTMCandidate, ∃ x : BitString, FailureAt M x

theorem universalSATLowerBound_iff_universalFailure :
    UniversalSATLowerBound ↔ UniversalFailure SATTarget := by
  rfl

theorem universalSATLowerBound_iff_notInP :
    UniversalSATLowerBound ↔ ¬ InP SATTarget := by
  rw [universalSATLowerBound_iff_universalFailure]
  exact universal_failure_iff_not_in_p

/-- Operational normal form: every candidate must either overrun its declared
clock on some input or answer SAT incorrectly on some input. -/
theorem universalSATLowerBound_iff_operational :
    UniversalSATLowerBound ↔
      ∀ M : PolyDTMCandidate,
        ∃ x : BitString,
          ¬ HaltsAtDeclaredBound M x ∨ SemanticMismatch M x := by
  constructor
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (failureAt_iff_nonhalting_or_mismatch M x).mp hx⟩
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (failureAt_iff_nonhalting_or_mismatch M x).mpr hx⟩

/-- Since PolyDTMCandidate already stores a proof that its time bound is
polynomial, a semantic-only strategy may focus on mismatch when halting is
known at the declared bound. -/
structure TotalClockedCandidate (M : PolyDTMCandidate) : Prop where
  halts : ∀ x : BitString, HaltsAtDeclaredBound M x

theorem failureAt_of_totalClocked_iff_mismatch
    (M : PolyDTMCandidate)
    (hTotal : TotalClockedCandidate M)
    (x : BitString) :
    FailureAt M x ↔ SemanticMismatch M x := by
  rw [failureAt_iff_nonhalting_or_mismatch]
  simp [hTotal.halts x]

/-- A semantic adversary for every total-clocked candidate. -/
structure SemanticAdversary where
  counterexample : PolyDTMCandidate → BitString
  mismatch :
    ∀ M : PolyDTMCandidate,
      TotalClockedCandidate M →
      SemanticMismatch M (counterexample M)

/-- If every candidate is known to halt at its declared clock, a semantic
adversary is enough for the full lower bound. -/
theorem semanticAdversary_closes
    (A : SemanticAdversary)
    (hTotal : ∀ M : PolyDTMCandidate, TotalClockedCandidate M) :
    UniversalSATLowerBound := by
  intro M
  refine ⟨A.counterexample M, ?_⟩
  exact (failureAt_of_totalClocked_iff_mismatch M (hTotal M) _).mpr
    (A.mismatch M (hTotal M))

/-- Direct selector normal form, definitionally aligned with the P02 operator. -/
structure UniversalFailureSelector where
  choose : PolyDTMCandidate → BitString
  fails : ∀ M : PolyDTMCandidate, FailureAt M (choose M)

def UniversalFailureSelector.toP02Producer
    (S : UniversalFailureSelector) :
    CanonicalSATP02Producer :=
  { counterexample := S.choose
    sound := S.fails }

theorem selector_closes_notInP
    (S : UniversalFailureSelector) :
    ¬ InP SATTarget := by
  exact canonicalSATProducer_iff_notInP.mp ⟨S.toP02Producer⟩

end P02UniversalLowerBound
end Real
end MCore
