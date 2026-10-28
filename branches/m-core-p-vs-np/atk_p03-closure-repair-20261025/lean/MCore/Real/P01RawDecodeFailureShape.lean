import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01RawDecodeFailureShape

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1

/-- Exact structural reasons why the recursive canonical decoder can return
none.  The constructors mirror decodeCircuitCore definitionally; no semantic
or machine hypothesis is stored here. -/
inductive RawDecodeFailure : (fuel : Nat) → BitString → Prop
  | fuelZero (bits : BitString) :
      RawDecodeFailure 0 bits
  | short0 (fuel : Nat) :
      RawDecodeFailure (fuel + 1) []
  | short1 (fuel : Nat) (b0 : Bool) :
      RawDecodeFailure (fuel + 1) [b0]
  | short2 (fuel : Nat) (b0 b1 : Bool) :
      RawDecodeFailure (fuel + 1) [b0, b1]
  | invalid110 (fuel : Nat) (rest : BitString) :
      RawDecodeFailure (fuel + 1) (true :: true :: false :: rest)
  | invalid111 (fuel : Nat) (rest : BitString) :
      RawDecodeFailure (fuel + 1) (true :: true :: true :: rest)
  | inputUnary
      (fuel : Nat) (rest : BitString)
      (h : decodeNat rest = none) :
      RawDecodeFailure (fuel + 1) (false :: false :: false :: rest)
  | notChild
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawDecodeFailure (fuel + 1) (false :: true :: true :: rest)
  | andLeft
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawDecodeFailure (fuel + 1) (true :: false :: false :: rest)
  | andRight
      (fuel : Nat) (rest : BitString)
      (left : Circuit) (rightSource : BitString)
      (hleft :
        decodeCircuitCore fuel rest = some (left, rightSource))
      (hright :
        decodeCircuitCore fuel rightSource = none) :
      RawDecodeFailure (fuel + 1) (true :: false :: false :: rest)
  | orLeft
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawDecodeFailure (fuel + 1) (true :: false :: true :: rest)
  | orRight
      (fuel : Nat) (rest : BitString)
      (left : Circuit) (rightSource : BitString)
      (hleft :
        decodeCircuitCore fuel rest = some (left, rightSource))
      (hright :
        decodeCircuitCore fuel rightSource = none) :
      RawDecodeFailure (fuel + 1) (true :: false :: true :: rest)

/-- Completeness of the structural failure classification. -/
theorem rawDecodeFailure_of_none :
    ∀ (fuel : Nat) (bits : BitString),
      decodeCircuitCore fuel bits = none →
        RawDecodeFailure fuel bits := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits h
      exact .fuelZero bits
  | succ fuel ih =>
      intro bits h
      cases bits with
      | nil =>
          exact .short0 fuel
      | cons b0 tail0 =>
          cases tail0 with
          | nil =>
              exact .short1 fuel b0
          | cons b1 tail1 =>
              cases tail1 with
              | nil =>
                  exact .short2 fuel b0 b1
              | cons b2 rest =>
                  cases b0 with
                  | false =>
                      cases b1 with
                      | false =>
                          cases b2 with
                          | false =>
                              cases hn : decodeNat rest with
                              | none =>
                                  exact .inputUnary fuel rest (by
                                    simpa using hn)
                              | some p =>
                                  simp [decodeCircuitCore, hn] at h
                          | true =>
                              simp [decodeCircuitCore] at h
                      | true =>
                          cases b2 with
                          | false =>
                              simp [decodeCircuitCore] at h
                          | true =>
                              cases hc : decodeCircuitCore fuel rest with
                              | none =>
                                  exact .notChild fuel rest (by
                                    simpa using hc)
                              | some p =>
                                  simp [decodeCircuitCore, hc] at h
                  | true =>
                      cases b1 with
                      | false =>
                          cases b2 with
                          | false =>
                              cases hl : decodeCircuitCore fuel rest with
                              | none =>
                                  exact .andLeft fuel rest (by
                                    simpa using hl)
                              | some p =>
                                  rcases p with ⟨left, rightSource⟩
                                  cases hr :
                                      decodeCircuitCore fuel rightSource with
                                  | none =>
                                      exact .andRight fuel rest left rightSource
                                        (by simpa using hl) (by simpa using hr)
                                  | some q =>
                                      simp [decodeCircuitCore, hl, hr] at h
                          | true =>
                              cases hl : decodeCircuitCore fuel rest with
                              | none =>
                                  exact .orLeft fuel rest (by
                                    simpa using hl)
                              | some p =>
                                  rcases p with ⟨left, rightSource⟩
                                  cases hr :
                                      decodeCircuitCore fuel rightSource with
                                  | none =>
                                      exact .orRight fuel rest left rightSource
                                        (by simpa using hl) (by simpa using hr)
                                  | some q =>
                                      simp [decodeCircuitCore, hl, hr] at h
                      | true =>
                          cases b2 with
                          | false =>
                              exact .invalid110 fuel rest
                          | true =>
                              exact .invalid111 fuel rest

/-- Whole-source malformed inputs split exactly into a recursive decoder failure
or a successfully decoded canonical prefix followed by nonempty residual bits. -/
inductive WholeDecodeFailure (bits : BitString) : Prop
  | core
      (h : RawDecodeFailure (bits.length + 1) bits) :
      WholeDecodeFailure bits
  | residual
      (phi : Circuit) (b : Bool) (tail : BitString)
      (h :
        decodeCircuitCore (bits.length + 1) bits =
          some (phi, b :: tail)) :
      WholeDecodeFailure bits

theorem decodeCircuit_none_has_failure
    (bits : BitString)
    (h : decodeCircuit bits = none) :
    WholeDecodeFailure bits := by
  unfold decodeCircuit at h
  cases hc :
      decodeCircuitCore (bits.length + 1) bits with
  | none =>
      exact .core
        (rawDecodeFailure_of_none
          (bits.length + 1) bits (by simpa using hc))
  | some p =>
      rcases p with ⟨phi, tail⟩
      cases tail with
      | nil =>
          simp [hc] at h
      | cons b bs =>
          exact .residual phi b bs (by simpa using hc)

#print axioms MCore.Real.P01RawDecodeFailureShape.rawDecodeFailure_of_none
#print axioms MCore.Real.P01RawDecodeFailureShape.decodeCircuit_none_has_failure

end P01RawDecodeFailureShape
end Real
end MCore
