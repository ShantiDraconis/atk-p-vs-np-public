import Mathlib.Tactic.DeriveCountable
import Mathlib.Basic.Countable.Basic
import MCore.Real.P02FiniteClockCandidateModel

namespace MCore
namespace Real
namespace P02FiniteClockCountability

open CanonicalFinalProof
open P02FiniteClockCandidateModel

instance directionCountable : Countable Direction := by
  let code : Direction → Nat
    | .left => 0
    | .stay => 1
    | .right => 2
  have hcode : Function.Injective code := by
    intro a b h
    cases a <;> cases b <;> simp [code] at h ⊢
  exact hcode.countable

/-- A finite description of the corrected deterministic candidate.
The blank symbol is omitted because the canonical candidate invariant fixes it
to none. All remaining machine tables live on finite domains. -/
structure FiniteClockDTMDescription where
  stateCount : Nat
  initial : Fin (stateCount + 1)
  transition :
    Fin (stateCount + 1) →
      Option Bool →
        Fin (stateCount + 1) × Option Bool × Direction
  halting : Fin (stateCount + 1) → Bool
  accepting : Fin (stateCount + 1) → Bool
  coefficient : Nat
  exponent : Nat
  deriving Countable

def describe
    (C : FiniteClockDTMCandidate) :
    FiniteClockDTMDescription :=
  { stateCount := C.stateCount
    initial := C.machine.initial
    transition := C.machine.transition
    halting := C.machine.halting
    accepting := C.accepting
    coefficient := C.coefficient
    exponent := C.exponent }

def realize
    (D : FiniteClockDTMDescription) :
    FiniteClockDTMCandidate :=
  { stateCount := D.stateCount
    machine :=
      { initial := D.initial
        blank := none
        transition := D.transition
        halting := D.halting }
    blank_none := rfl
    accepting := D.accepting
    coefficient := D.coefficient
    exponent := D.exponent }

theorem realize_describe
    (C : FiniteClockDTMCandidate) :
    realize (describe C) = C := by
  rcases C with ⟨n, M, hblank, accepting, coefficient, exponent⟩
  rcases M with ⟨initial, blank, transition, halting⟩
  dsimp at hblank
  subst blank
  rfl

theorem describe_injective :
    Function.Injective describe := by
  intro A B h
  calc
    A = realize (describe A) := (realize_describe A).symm
    _ = realize (describe B) := congrArg realize h
    _ = B := realize_describe B

noncomputable instance finiteClockDTMCandidateCountable :
    Countable FiniteClockDTMCandidate :=
  describe_injective.countable

theorem finite_clock_candidate_countable :
    Countable FiniteClockDTMCandidate :=
  inferInstance

#print axioms MCore.Real.P02FiniteClockCountability.realize_describe
#print axioms MCore.Real.P02FiniteClockCountability.describe_injective
#print axioms MCore.Real.P02FiniteClockCountability.finite_clock_candidate_countable

end P02FiniteClockCountability
end Real
end MCore
