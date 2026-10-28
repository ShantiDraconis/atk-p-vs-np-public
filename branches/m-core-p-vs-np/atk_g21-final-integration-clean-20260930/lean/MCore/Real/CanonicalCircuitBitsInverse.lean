import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace CanonicalCircuitBitsInverse

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits

/-- Successful unary decoding determines the exact consumed prefix. -/
theorem decodeNat_inverse
    (bits : BitString)
    (n : Nat)
    (tail : BitString)
    (h : decodeNat bits = some (n, tail)) :
    bits = encodeNat n ++ tail := by
  induction bits generalizing n tail with
  | nil =>
      simp [decodeNat] at h
  | cons b rest ih =>
      cases b with
      | false =>
          simp [decodeNat] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hrest : decodeNat rest with
          | none =>
              simp [decodeNat, hrest] at h
          | some p =>
              rcases p with ⟨k, t⟩
              simp [decodeNat, hrest] at h
              rcases h with ⟨rfl, rfl⟩
              have hInv := ih k t hrest
              simp [encodeNat, hInv]

/-- Successful recursive decoding determines the exact canonical prefix and
the exact residual tail.  This is the converse direction needed to prevent a
machine parser from accepting a non-canonical representation of a Circuit. -/
theorem decodeCircuitCore_inverse
    (fuel : Nat)
    (bits : BitString)
    (c : Circuit)
    (tail : BitString)
    (h : decodeCircuitCore fuel bits = some (c, tail)) :
    bits = encodeCircuit c ++ tail := by
  induction fuel generalizing bits c tail with
  | zero =>
      simp [decodeCircuitCore] at h
  | succ fuel ih =>
      cases bits with
      | nil =>
          simp [decodeCircuitCore] at h
      | cons b1 r1 =>
          cases r1 with
          | nil =>
              simp [decodeCircuitCore] at h
          | cons b2 r2 =>
              cases r2 with
              | nil =>
                  simp [decodeCircuitCore] at h
              | cons b3 rest =>
                  cases b1 <;> cases b2 <;> cases b3
                  · -- 000 : input
                    cases hn : decodeNat rest with
                    | none =>
                        simp [decodeCircuitCore, hn] at h
                    | some p =>
                        rcases p with ⟨i, t⟩
                        simp [decodeCircuitCore, hn] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hNat := decodeNat_inverse rest i t hn
                        simp [encodeCircuit, hNat, List.append_assoc]
                  · -- 001 : const false
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 010 : const true
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 011 : not
                    cases hc : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, hc] at h
                    | some p =>
                        rcases p with ⟨child, t⟩
                        simp [decodeCircuitCore, hc] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hChild := ih rest child t hc
                        simp [encodeCircuit, hChild, List.append_assoc]
                  · -- 100 : and
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b, t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hA := ih rest a rest' ha
                            have hB := ih rest' b t hb
                            simp [encodeCircuit, hA, hB, List.append_assoc]
                  · -- 101 : or
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b, t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hA := ih rest a rest' ha
                            have hB := ih rest' b t hb
                            simp [encodeCircuit, hA, hB, List.append_assoc]
                  · -- 110 : invalid
                    simp [decodeCircuitCore] at h
                  · -- 111 : invalid
                    simp [decodeCircuitCore] at h

/-- Exact inverse for the total canonical decoder: successful decoding implies
that the whole input is exactly the canonical encoding, with no residual bits. -/
theorem decodeCircuit_inverse
    (bits : BitString)
    (c : Circuit)
    (h : decodeCircuit bits = some c) :
    bits = encodeCircuit c := by
  unfold decodeCircuit at h
  cases hc : decodeCircuitCore (bits.length + 1) bits with
  | none =>
      simp [hc] at h
  | some p =>
      rcases p with ⟨c', tail⟩
      cases tail with
      | nil =>
          simp [hc] at h
          subst c'
          simpa using
            (decodeCircuitCore_inverse (bits.length + 1) bits c [] hc)
      | cons b bs =>
          simp [hc] at h

/-- Canonical decoding is therefore exact, not merely a left inverse on
encoded circuits. -/
theorem decodeCircuit_eq_some_iff
    (bits : BitString)
    (c : Circuit) :
    decodeCircuit bits = some c ↔ bits = encodeCircuit c := by
  constructor
  · exact decodeCircuit_inverse bits c
  · intro h
    subst bits
    exact decodeCircuit_encode c

/-- The parser correctness target can now be stated as exact membership in the
range of encodeCircuit. -/
theorem exists_decodeCircuit_iff_exists_exact_encoding
    (bits : BitString) :
    (∃ c : Circuit, decodeCircuit bits = some c) ↔
      ∃ c : Circuit, bits = encodeCircuit c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, decodeCircuit_inverse bits c hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, decodeCircuit_encode c⟩

theorem encodeCircuit_injective
    {a b : Circuit}
    (h : encodeCircuit a = encodeCircuit b) :
    a = b := by
  have ha : decodeCircuit (encodeCircuit a) = some a :=
    decodeCircuit_encode a
  have hb : decodeCircuit (encodeCircuit b) = some b :=
    decodeCircuit_encode b
  rw [h] at ha
  rw [decodeCircuit_encode b] at ha
  exact (Option.some.inj ha).symm

#print axioms MCore.Real.CanonicalCircuitBitsInverse.decodeNat_inverse
#print axioms MCore.Real.CanonicalCircuitBitsInverse.decodeCircuitCore_inverse
#print axioms MCore.Real.CanonicalCircuitBitsInverse.decodeCircuit_inverse
#print axioms MCore.Real.CanonicalCircuitBitsInverse.decodeCircuit_eq_some_iff
#print axioms MCore.Real.CanonicalCircuitBitsInverse.exists_decodeCircuit_iff_exists_exact_encoding
#print axioms MCore.Real.CanonicalCircuitBitsInverse.encodeCircuit_injective

end CanonicalCircuitBitsInverse
end Real
end MCore
