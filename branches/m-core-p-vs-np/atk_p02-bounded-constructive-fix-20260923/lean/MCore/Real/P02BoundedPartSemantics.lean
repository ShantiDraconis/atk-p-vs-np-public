import Mathlib.Computability.PartrecCode
import MCore.Real.P02BoundedSemanticInput
import MCore.Real.P02BoundedDomain

namespace MCore
namespace Real
namespace P02BoundedPartSemantics

open P02BoundedSemanticInput
open P02BoundedDomain

/--
Semantic divergence at the distinguished input.
This lives in `Part Nat`: the computation has no value.
No decidability claim is made for this predicate.
-/
def DivergesAtZero (c : Nat.Partrec.Code) : Prop :=
  c.eval 0 = (⊥ : Part Nat)

/--
Finite observation state at a fixed fuel.  This is constructive because
`evaln` is total and returns an `Option Nat`.
-/
inductive FuelState where
  | pending
  | decided (v : Nat)
  deriving DecidableEq, Repr

def fuelState (fuel : Nat) (c : Nat.Partrec.Code) : FuelState :=
  match c.evaln fuel 0 with
  | none => .pending
  | some v => .decided v

@[simp] theorem fuelState_pending_iff
    (fuel : Nat) (c : Nat.Partrec.Code) :
    fuelState fuel c = .pending ↔ c.evaln fuel 0 = none := by
  unfold fuelState
  cases h : c.evaln fuel 0 <;> simp [h]

@[simp] theorem fuelState_decided_iff
    (fuel : Nat) (c : Nat.Partrec.Code) (v : Nat) :
    fuelState fuel c = .decided v ↔ c.evaln fuel 0 = some v := by
  unfold fuelState
  cases h : c.evaln fuel 0 <;> simp [h]

/--
A concrete bounded witness is exactly a decided finite observation.
This is the constructive domain used by the bounded lane.
-/
theorem domFuel_iff_decided
    (fuel : Nat) (c : Nat.Partrec.Code) :
    DomFuel fuel c ↔ ∃ v, fuelState fuel c = .decided v := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (fuelState_decided_iff fuel c v).2 hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, (fuelState_decided_iff fuel c v).1 hv⟩

/--
Once a bounded evaluation has produced a value, increasing the fuel cannot
send it back to the pending state.
-/
theorem decided_mono
    {fuel₁ fuel₂ : Nat}
    (hFuel : fuel₁ ≤ fuel₂)
    {c : Nat.Partrec.Code}
    {v : Nat}
    (h : c.evaln fuel₁ 0 = some v) :
    c.evaln fuel₂ 0 = some v := by
  exact Nat.Partrec.Code.evaln_mono hFuel h

theorem domFuel_mono_constructive
    {fuel₁ fuel₂ : Nat}
    (hFuel : fuel₁ ≤ fuel₂)
    {c : Nat.Partrec.Code}
    (h : DomFuel fuel₁ c) :
    DomFuel fuel₂ c := by
  rcases h with ⟨v, hv⟩
  exact ⟨v, decided_mono hFuel hv⟩

/--
If no value is visible at fuel n, then no smaller fuel can already have
produced a value.  This is the finite, constructive exclusion used by the
bounded lane; it does not decide semantic divergence.
-/
theorem none_downward
    {fuel n : Nat}
    (hFuel : fuel ≤ n)
    {c : Nat.Partrec.Code}
    (hnone : c.evaln n 0 = none) :
    c.evaln fuel 0 = none := by
  cases hsmall : c.evaln fuel 0 with
  | none => rfl
  | some v =>
      have hlarge : c.evaln n 0 = some v :=
        decided_mono hFuel hsmall
      rw [hnone] at hlarge
      contradiction

/--
Finite dichotomy at fuel n: either a value has been observed, or every
smaller/equal fuel is still pending.  This uses only decidability of Option,
not excluded middle over `Part.Dom`.
-/
theorem bounded_observation_dichotomy
    (n : Nat) (c : Nat.Partrec.Code) :
    (∃ v, c.evaln n 0 = some v) ∨
      (∀ fuel, fuel ≤ n → c.evaln fuel 0 = none) := by
  cases h : c.evaln n 0 with
  | some v =>
      exact Or.inl ⟨v, h⟩
  | none =>
      exact Or.inr (fun fuel hf => none_downward hf h)

/--
Semantic bottom implies that no finite evaluator can return a value.
The converse is intentionally not packaged as a decidable test.
-/
theorem divergence_implies_all_evaln_none
    {c : Nat.Partrec.Code}
    (hdiv : DivergesAtZero c) :
    ∀ fuel, c.evaln fuel 0 = none := by
  intro fuel
  cases h : c.evaln fuel 0 with
  | none => rfl
  | some v =>
      have hvPart : v ∈ c.eval 0 := Nat.Partrec.Code.evaln_sound h
      rw [DivergesAtZero, hdiv] at hvPart
      exact (Part.not_mem_none v hvPart).elim

#print axioms MCore.Real.P02BoundedPartSemantics.domFuel_iff_decided
#print axioms MCore.Real.P02BoundedPartSemantics.decided_mono
#print axioms MCore.Real.P02BoundedPartSemantics.domFuel_mono_constructive
#print axioms MCore.Real.P02BoundedPartSemantics.none_downward
#print axioms MCore.Real.P02BoundedPartSemantics.bounded_observation_dichotomy
#print axioms MCore.Real.P02BoundedPartSemantics.divergence_implies_all_evaln_none

end P02BoundedPartSemantics
end Real
end MCore
