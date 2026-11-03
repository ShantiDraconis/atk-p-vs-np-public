import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01DecodeCoreLaws

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits

theorem decodeNat_sound
    (bits : BitString) (n : Nat) (tail : BitString)
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
          cases hr : decodeNat rest with
          | none =>
              simp [decodeNat, hr] at h
          | some p =>
              rcases p with ⟨m, t⟩
              simp [decodeNat, hr] at h
              rcases h with ⟨rfl, rfl⟩
              have hs := ih m t hr
              simp [encodeNat, hs, List.append_assoc]


theorem decodeNat_none_eq_replicate_true
    (bits : BitString)
    (h : decodeNat bits = none) :
    bits = List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | false =>
          simp [decodeNat] at h
      | true =>
          cases hr : decodeNat rest with
          | none =>
              have hs := ih hr
              rw [hs]
              simp [List.replicate_succ]
          | some p =>
              simp [decodeNat, hr] at h

theorem decodeCircuitCore_sound
    (fuel : Nat) (bits : BitString)
    (phi : Circuit) (tail : BitString)
    (h : decodeCircuitCore fuel bits = some (phi, tail)) :
    bits = encodeCircuit phi ++ tail := by
  induction fuel generalizing bits phi tail with
  | zero =>
      simp [decodeCircuitCore] at h
  | succ fuel ih =>
      cases bits with
      | nil =>
          simp [decodeCircuitCore] at h
      | cons b0 r0 =>
          cases r0 with
          | nil =>
              simp [decodeCircuitCore] at h
          | cons b1 r1 =>
              cases r1 with
              | nil =>
                  simp [decodeCircuitCore] at h
              | cons b2 rest =>
                  cases b0 <;> cases b1 <;> cases b2
                  · -- 000 input
                    cases hn : decodeNat rest with
                    | none =>
                        simp [decodeCircuitCore, hn] at h
                    | some p =>
                        rcases p with ⟨i,t⟩
                        simp [decodeCircuitCore, hn] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hs := decodeNat_sound rest i t hn
                        simp [encodeCircuit, hs, List.append_assoc]
                  · -- 001 const false
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 010 const true
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 011 not
                    cases hc : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, hc] at h
                    | some p =>
                        rcases p with ⟨c,t⟩
                        simp [decodeCircuitCore, hc] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hs := ih rest c t hc
                        simp [encodeCircuit, hs, List.append_assoc]
                  · -- 100 and
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a,rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b,t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b t hb
                            simp [encodeCircuit, hsa, hsb, List.append_assoc]
                  · -- 101 or
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a,rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b,t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b t hb
                            simp [encodeCircuit, hsa, hsb, List.append_assoc]
                  · -- 110 invalid
                    simp [decodeCircuitCore] at h
                  · -- 111 invalid
                    simp [decodeCircuitCore] at h

theorem decodeCircuitCore_size_lt
    (fuel : Nat) (bits : BitString)
    (phi : Circuit) (tail : BitString)
    (h : decodeCircuitCore fuel bits = some (phi, tail)) :
    CircuitK1.size phi < fuel := by
  induction fuel generalizing bits phi tail with
  | zero =>
      simp [decodeCircuitCore] at h
  | succ fuel ih =>
      cases bits with
      | nil =>
          simp [decodeCircuitCore] at h
      | cons b0 r0 =>
          cases r0 with
          | nil =>
              simp [decodeCircuitCore] at h
          | cons b1 r1 =>
              cases r1 with
              | nil =>
                  simp [decodeCircuitCore] at h
              | cons b2 rest =>
                  cases b0 <;> cases b1 <;> cases b2
                  · cases hn : decodeNat rest with
                    | none => simp [decodeCircuitCore, hn] at h
                    | some p =>
                        rcases p with ⟨i,t⟩
                        simp [decodeCircuitCore, hn] at h
                        rcases h with ⟨rfl, rfl⟩
                        simp [CircuitK1.size]
                  · simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    simp [CircuitK1.size]
                  · simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    simp [CircuitK1.size]
                  · cases hc : decodeCircuitCore fuel rest with
                    | none => simp [decodeCircuitCore, hc] at h
                    | some p =>
                        rcases p with ⟨c,t⟩
                        simp [decodeCircuitCore, hc] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hs := ih rest c t hc
                        simp [CircuitK1.size]
                        omega
                  · cases ha : decodeCircuitCore fuel rest with
                    | none => simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a,rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none => simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b,t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b t hb
                            simp [CircuitK1.size]
                            omega
                  · cases ha : decodeCircuitCore fuel rest with
                    | none => simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a,rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none => simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b,t⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b t hb
                            simp [CircuitK1.size]
                            omega
                  · simp [decodeCircuitCore] at h
                  · simp [decodeCircuitCore] at h


theorem decodeCircuit_sound
    (bits : BitString) (phi : Circuit)
    (h : decodeCircuit bits = some phi) :
    bits = encodeCircuit phi := by
  unfold decodeCircuit at h
  cases hc : decodeCircuitCore (bits.length + 1) bits with
  | none =>
      simp [hc] at h
  | some p =>
      rcases p with ⟨c,tail⟩
      cases tail with
      | nil =>
          simp [hc] at h
          subst c
          have hs :=
            decodeCircuitCore_sound (bits.length + 1) bits phi [] hc
          simpa using hs
      | cons b rest =>
          simp [hc] at h

theorem decodeCircuitCore_some_mono
    {fuel fuel' : Nat} (hff : fuel ≤ fuel')
    {bits : BitString} {phi : Circuit} {tail : BitString}
    (h : decodeCircuitCore fuel bits = some (phi, tail)) :
    decodeCircuitCore fuel' bits = some (phi, tail) := by
  have hshape := decodeCircuitCore_sound fuel bits phi tail h
  have hsize := decodeCircuitCore_size_lt fuel bits phi tail h
  have hsize' : CircuitK1.size phi < fuel' :=
    Nat.lt_of_lt_of_le hsize hff
  rw [hshape]
  exact decodeCircuitCore_encode_append phi tail fuel' hsize'

theorem decodeCircuitCore_none_of_larger_none
    {fuel fuel' : Nat} (hff : fuel ≤ fuel')
    {bits : BitString}
    (h : decodeCircuitCore fuel' bits = none) :
    decodeCircuitCore fuel bits = none := by
  cases hs : decodeCircuitCore fuel bits with
  | none => exact hs
  | some p =>
      rcases p with ⟨phi,tail⟩
      have hmono := decodeCircuitCore_some_mono hff hs
      rw [h] at hmono
      contradiction

#print axioms MCore.Real.P01DecodeCoreLaws.decodeNat_sound
#print axioms MCore.Real.P01DecodeCoreLaws.decodeCircuitCore_sound
#print axioms MCore.Real.P01DecodeCoreLaws.decodeCircuitCore_size_lt
#print axioms MCore.Real.P01DecodeCoreLaws.decodeCircuitCore_some_mono
#print axioms MCore.Real.P01DecodeCoreLaws.decodeCircuitCore_none_of_larger_none

end P01DecodeCoreLaws
end Real
end MCore
