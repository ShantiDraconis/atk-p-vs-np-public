import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01RawDecodeFailureCases

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits

/-- Exact structural reasons why one bounded raw decoder call can fail.
The constructors mirror `decodeCircuitCore` one-for-one. -/
inductive RawFailureCase : Nat → BitString → Type
  | fuelZero
      (bits : BitString) :
      RawFailureCase 0 bits
  | short
      (fuel : Nat) (bits : BitString)
      (hshort : bits.length < 3) :
      RawFailureCase (fuel + 1) bits
  | invalid110
      (fuel : Nat) (rest : BitString) :
      RawFailureCase (fuel + 1) (true :: true :: false :: rest)
  | invalid111
      (fuel : Nat) (rest : BitString) :
      RawFailureCase (fuel + 1) (true :: true :: true :: rest)
  | inputUnary
      (fuel : Nat) (rest : BitString)
      (hdec : decodeNat rest = none) :
      RawFailureCase (fuel + 1) (false :: false :: false :: rest)
  | negChild
      (fuel : Nat) (rest : BitString)
      (hchild : decodeCircuitCore fuel rest = none) :
      RawFailureCase (fuel + 1) (false :: true :: true :: rest)
  | andLeft
      (fuel : Nat) (rest : BitString)
      (hleft : decodeCircuitCore fuel rest = none) :
      RawFailureCase (fuel + 1) (true :: false :: false :: rest)
  | andRight
      (fuel : Nat) (rest rest' : BitString) (left : Circuit)
      (hleft : decodeCircuitCore fuel rest = some (left, rest'))
      (hright : decodeCircuitCore fuel rest' = none) :
      RawFailureCase (fuel + 1) (true :: false :: false :: rest)
  | orLeft
      (fuel : Nat) (rest : BitString)
      (hleft : decodeCircuitCore fuel rest = none) :
      RawFailureCase (fuel + 1) (true :: false :: true :: rest)
  | orRight
      (fuel : Nat) (rest rest' : BitString) (left : Circuit)
      (hleft : decodeCircuitCore fuel rest = some (left, rest'))
      (hright : decodeCircuitCore fuel rest' = none) :
      RawFailureCase (fuel + 1) (true :: false :: true :: rest)

/-- Decoder failure has exactly one of the structural causes above. -/
theorem decodeCircuitCore_none_cases
    (fuel : Nat) (bits : BitString)
    (h : decodeCircuitCore fuel bits = none) :
    RawFailureCase fuel bits := by
  cases fuel with
  | zero =>
      exact .fuelZero bits
  | succ f =>
      cases bits with
      | nil =>
          exact .short f [] (by simp)
      | cons b0 r0 =>
          cases r0 with
          | nil =>
              exact .short f [b0] (by simp)
          | cons b1 r1 =>
              cases r1 with
              | nil =>
                  exact .short f [b0, b1] (by simp)
              | cons b2 rest =>
                  cases b0 <;> cases b1 <;> cases b2
                  · -- 000 input
                    cases hd : decodeNat rest with
                    | none =>
                        exact .inputUnary f rest hd
                    | some p =>
                        rcases p with ⟨i, tail⟩
                        simp [decodeCircuitCore, hd] at h
                  · -- 001 const false: cannot structurally fail
                    simp [decodeCircuitCore] at h
                  · -- 010 const true
                    simp [decodeCircuitCore] at h
                  · -- 011 neg
                    cases hc : decodeCircuitCore f rest with
                    | none =>
                        exact .negChild f rest hc
                    | some p =>
                        rcases p with ⟨c, tail⟩
                        simp [decodeCircuitCore, hc] at h
                  · -- 100 and
                    cases hl : decodeCircuitCore f rest with
                    | none =>
                        exact .andLeft f rest hl
                    | some p =>
                        rcases p with ⟨left, rest'⟩
                        cases hr : decodeCircuitCore f rest' with
                        | none =>
                            exact .andRight f rest rest' left hl hr
                        | some p2 =>
                            rcases p2 with ⟨right, tail⟩
                            simp [decodeCircuitCore, hl, hr] at h
                  · -- 101 or
                    cases hl : decodeCircuitCore f rest with
                    | none =>
                        exact .orLeft f rest hl
                    | some p =>
                        rcases p with ⟨left, rest'⟩
                        cases hr : decodeCircuitCore f rest' with
                        | none =>
                            exact .orRight f rest rest' left hl hr
                        | some p2 =>
                            rcases p2 with ⟨right, tail⟩
                            simp [decodeCircuitCore, hl, hr] at h
                  · exact .invalid110 f rest
                  · exact .invalid111 f rest

/-- Input-unary failure is exactly the already-certified all-true truncated
payload shape. -/
theorem inputUnary_payload_all_true
    {rest : BitString}
    (h : decodeNat rest = none) :
    rest = List.replicate rest.length true := by
  induction rest with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          simp [decodeNat] at h
      | true =>
          cases hb : decodeNat bs with
          | none =>
              have htail := ih hb
              rw [htail]
              simp [List.replicate_succ]
          | some p =>
              simp [decodeNat, hb] at h

#print axioms MCore.Real.P01RawDecodeFailureCases.decodeCircuitCore_none_cases
#print axioms MCore.Real.P01RawDecodeFailureCases.inputUnary_payload_all_true

end P01RawDecodeFailureCases
end Real
end MCore
