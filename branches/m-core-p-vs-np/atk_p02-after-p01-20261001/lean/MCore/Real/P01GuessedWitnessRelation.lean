import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01GuessedWitnessRelation

/-!
# SATBits as a guessed fixed-length witness relation

Pure logic, no machine.  The integrated P01 machine guesses exactly
`bs.length` witness bits (the witness-guess phase uses the source block as its
ruler).  This module proves that this is exactly SAT:

  `SATBits circuitBitEncoding bs ↔ ∃ w, w.length = bs.length ∧ VerifyBits bs w`

The forward direction needs decoder soundness (`decodeCircuit bs = some φ →
bs = encodeCircuit φ`), which was not yet in the repository; it is proved
here by structural recursion on the decoder.
-/

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open CanonicalSATWitness

theorem decodeNat_sound :
    ∀ (bits : BitString) (n : Nat) (tail : BitString),
      decodeNat bits = some (n, tail) → bits = encodeNat n ++ tail
  | [], _, _, h => by simp [decodeNat] at h
  | false :: rest, n, tail, h => by
      simp [decodeNat] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | true :: rest, n, tail, h => by
      simp only [decodeNat] at h
      cases hr : decodeNat rest with
      | none => simp [hr] at h
      | some p =>
          rcases p with ⟨m, t⟩
          simp [hr] at h
          rcases h with ⟨rfl, rfl⟩
          simp [encodeNat, decodeNat_sound rest m t hr]

theorem decodeCircuitCore_sound :
    ∀ (fuel : Nat) (bits : BitString) (c : Circuit) (rest : BitString),
      decodeCircuitCore fuel bits = some (c, rest) → bits = encodeCircuit c ++ rest
  | 0, _, _, _, h => by simp [decodeCircuitCore] at h
  | fuel + 1, bits, c, rest, h => by
      rcases bits with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩
      · simp [decodeCircuitCore] at h
      · cases b1 <;> simp [decodeCircuitCore] at h
      · cases b1 <;> cases b2 <;> simp [decodeCircuitCore] at h
      · cases b1 <;> cases b2 <;> cases b3
        · -- input
          simp only [decodeCircuitCore] at h
          cases hr : decodeNat r with
          | none => simp [hr] at h
          | some p =>
              rcases p with ⟨i, t⟩
              simp [hr] at h
              rcases h with ⟨rfl, rfl⟩
              simp [encodeCircuit, decodeNat_sound r i t hr]
        · -- const false
          simp [decodeCircuitCore] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
        · -- const true
          simp [decodeCircuitCore] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
        · -- not
          simp only [decodeCircuitCore] at h
          cases hr : decodeCircuitCore fuel r with
          | none => simp [hr] at h
          | some p =>
              rcases p with ⟨a, t⟩
              simp [hr] at h
              rcases h with ⟨rfl, rfl⟩
              simp [encodeCircuit, decodeCircuitCore_sound fuel r a t hr]
        · -- and
          simp only [decodeCircuitCore] at h
          cases hr : decodeCircuitCore fuel r with
          | none => simp [hr] at h
          | some p =>
              rcases p with ⟨a, r'⟩
              cases hr' : decodeCircuitCore fuel r' with
              | none => simp [hr, hr'] at h
              | some q =>
                  rcases q with ⟨b, t⟩
                  simp [hr, hr'] at h
                  rcases h with ⟨rfl, rfl⟩
                  simp [encodeCircuit, decodeCircuitCore_sound fuel r a r' hr,
                    decodeCircuitCore_sound fuel r' b t hr']
        · -- or
          simp only [decodeCircuitCore] at h
          cases hr : decodeCircuitCore fuel r with
          | none => simp [hr] at h
          | some p =>
              rcases p with ⟨a, r'⟩
              cases hr' : decodeCircuitCore fuel r' with
              | none => simp [hr, hr'] at h
              | some q =>
                  rcases q with ⟨b, t⟩
                  simp [hr, hr'] at h
                  rcases h with ⟨rfl, rfl⟩
                  simp [encodeCircuit, decodeCircuitCore_sound fuel r a r' hr,
                    decodeCircuitCore_sound fuel r' b t hr']
        · simp [decodeCircuitCore] at h
        · simp [decodeCircuitCore] at h

/-- Decoder soundness: the canonical decoder only accepts canonical encodings. -/
theorem decodeCircuit_sound (bits : BitString) (φ : Circuit)
    (h : decodeCircuit bits = some φ) : bits = encodeCircuit φ := by
  unfold decodeCircuit at h
  cases hc : decodeCircuitCore (bits.length + 1) bits with
  | none => simp [hc] at h
  | some p =>
      rcases p with ⟨c, rest⟩
      cases rest with
      | nil =>
          simp [hc] at h
          subst h
          simpa using decodeCircuitCore_sound _ bits c [] hc
      | cons x xs => simp [hc] at h

theorem varBound_le_of_decode (bits : BitString) (φ : Circuit)
    (h : decodeCircuit bits = some φ) : varBound φ ≤ bits.length := by
  rw [decodeCircuit_sound bits φ h]
  exact varBound_le_encoded_length φ

/-- Bit-level verifier relation read by the physical verifier: the source
decodes to a CNF circuit that evaluates to true under the guessed bits
(indices past the witness read as `false`). -/
def VerifyBits (bs w : BitString) : Prop :=
  ∃ φ : Circuit,
    decodeCircuit bs = some φ ∧ IsCNF φ ∧
      evalCircuit (fun i => w.getD i false) φ = true

theorem getD_map_range (σ : Assignment) (n i : Nat) (hi : i < n) :
    ((List.range n).map σ).getD i false = σ i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- SAT over bits is exactly: some witness of the source's own length verifies. -/
theorem satBits_iff_guessed_witness (bs : BitString) :
    SATBits circuitBitEncoding bs ↔
      ∃ w : BitString, w.length = bs.length ∧ VerifyBits bs w := by
  constructor
  · rintro ⟨φ, hdec, hCNF, σ, heval⟩
    have hdec' : decodeCircuit bs = some φ := hdec
    refine ⟨(List.range bs.length).map σ, by simp, φ, hdec', hCNF, ?_⟩
    have hle := varBound_le_of_decode bs φ hdec'
    rw [← heval]
    apply evalCircuit_eq_of_agree_below
    intro i hi
    exact getD_map_range σ bs.length i (Nat.lt_of_lt_of_le hi hle)
  · rintro ⟨w, _, φ, hdec, hCNF, heval⟩
    exact ⟨φ, hdec, hCNF, fun i => w.getD i false, heval⟩

#print axioms decodeCircuit_sound
#print axioms satBits_iff_guessed_witness

end P01GuessedWitnessRelation
end Real
end MCore
