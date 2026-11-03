import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01CoreDecodeFailureAtoms

namespace MCore
namespace Real
namespace P01DecodeFailureLaws

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01CoreDecodeFailureAtoms

theorem decode_input_none_iff
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (false :: false :: false :: rest) = none ↔
      decodeNat rest = none := by
  simp [decodeCircuitCore]
  cases h : decodeNat rest <;> simp [h]

theorem decode_const_false_ne_none
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (false :: false :: true :: rest) ≠ none := by
  simp [decodeCircuitCore]

theorem decode_const_true_ne_none
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (false :: true :: false :: rest) ≠ none := by
  simp [decodeCircuitCore]

theorem decode_not_none_iff
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (false :: true :: true :: rest) = none ↔
      decodeCircuitCore fuel rest = none := by
  simp [decodeCircuitCore]
  cases h : decodeCircuitCore fuel rest <;> simp [h]

theorem decode_and_none_iff
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (true :: false :: false :: rest) = none ↔
      decodeCircuitCore fuel rest = none ∨
      ∃ a rest',
        decodeCircuitCore fuel rest = some (a, rest') ∧
        decodeCircuitCore fuel rest' = none := by
  simp only [decodeCircuitCore]
  cases h1 : decodeCircuitCore fuel rest with
  | none =>
      simp [h1]
  | some p =>
      rcases p with ⟨a, rest'⟩
      cases h2 : decodeCircuitCore fuel rest' with
      | none =>
          simp [h1, h2]
      | some q =>
          rcases q with ⟨b, tail⟩
          simp [h1, h2]

theorem decode_or_none_iff
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (true :: false :: true :: rest) = none ↔
      decodeCircuitCore fuel rest = none ∨
      ∃ a rest',
        decodeCircuitCore fuel rest = some (a, rest') ∧
        decodeCircuitCore fuel rest' = none := by
  simp only [decodeCircuitCore]
  cases h1 : decodeCircuitCore fuel rest with
  | none =>
      simp [h1]
  | some p =>
      rcases p with ⟨a, rest'⟩
      cases h2 : decodeCircuitCore fuel rest' with
      | none =>
          simp [h1, h2]
      | some q =>
          rcases q with ⟨b, tail⟩
          simp [h1, h2]

theorem decode_invalid_110_none
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (true :: true :: false :: rest) = none := by
  simp [decodeCircuitCore]

theorem decode_invalid_111_none
    (fuel : Nat) (rest : BitString) :
    decodeCircuitCore (fuel + 1)
        (true :: true :: true :: rest) = none := by
  simp [decodeCircuitCore]

/-- Complete semantic classifier for one nonzero-fuel decoder step. -/
theorem decodeCore_none_cases
    (fuel : Nat) (bits : BitString)
    (h : decodeCircuitCore (fuel + 1) bits = none) :
    bits.length < 3 ∨
    (∃ rest, bits = false :: false :: false :: rest ∧ decodeNat rest = none) ∨
    (∃ rest, bits = false :: true :: true :: rest ∧
      decodeCircuitCore fuel rest = none) ∨
    (∃ rest, bits = true :: false :: false :: rest ∧
      (decodeCircuitCore fuel rest = none ∨
        ∃ a rest',
          decodeCircuitCore fuel rest = some (a, rest') ∧
          decodeCircuitCore fuel rest' = none)) ∨
    (∃ rest, bits = true :: false :: true :: rest ∧
      (decodeCircuitCore fuel rest = none ∨
        ∃ a rest',
          decodeCircuitCore fuel rest = some (a, rest') ∧
          decodeCircuitCore fuel rest' = none)) ∨
    (∃ third rest, bits = true :: true :: third :: rest) := by
  rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, rest⟩⟩⟩
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · right
    cases b0 <;> cases b1 <;> cases b2
    · exact Or.inl ⟨rest, rfl, (decode_input_none_iff fuel rest).1 h⟩
    · exfalso
      exact (decode_const_false_ne_none fuel rest) h
    · exfalso
      exact (decode_const_true_ne_none fuel rest) h
    · exact Or.inr (Or.inl ⟨rest, rfl, (decode_not_none_iff fuel rest).1 h⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨rest, rfl, (decode_and_none_iff fuel rest).1 h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rest, rfl, (decode_or_none_iff fuel rest).1 h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨false, rest, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨true, rest, rfl⟩))))

#print axioms MCore.Real.P01DecodeFailureLaws.decode_input_none_iff
#print axioms MCore.Real.P01DecodeFailureLaws.decode_not_none_iff
#print axioms MCore.Real.P01DecodeFailureLaws.decode_and_none_iff
#print axioms MCore.Real.P01DecodeFailureLaws.decode_or_none_iff
#print axioms MCore.Real.P01DecodeFailureLaws.decodeCore_none_cases

end P01DecodeFailureLaws
end Real
end MCore
