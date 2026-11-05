import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace CanonicalSATWitness

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits

def varBound : Circuit → Nat
  | .input i => i + 1
  | .const _ => 0
  | .not c => varBound c
  | .and a b => max (varBound a) (varBound b)
  | .or a b => max (varBound a) (varBound b)

abbrev SATWitness (φ : Circuit) := Fin (varBound φ) → Bool

def assignmentOfWitness
    (φ : Circuit)
    (w : SATWitness φ) :
    Assignment :=
  fun i =>
    if h : i < varBound φ then
      w ⟨i, h⟩
    else
      false

theorem evalCircuit_eq_of_agree_below
    (φ : Circuit)
    (σ τ : Assignment)
    (hAgree : ∀ i, i < varBound φ → σ i = τ i) :
    evalCircuit σ φ = evalCircuit τ φ := by
  induction φ with
  | input i =>
      simp [varBound, evalCircuit, hAgree i (Nat.lt_succ_self i)]
  | const b =>
      rfl
  | not c ih =>
      have hSub : ∀ i, i < varBound c → σ i = τ i := by
        intro i hi
        exact hAgree i hi
      simp [varBound, evalCircuit, ih hSub]
  | and a b iha ihb =>
      have ha : ∀ i, i < varBound a → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hb : ∀ i, i < varBound b → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
      simp [varBound, evalCircuit, iha ha, ihb hb]
  | or a b iha ihb =>
      have ha : ∀ i, i < varBound a → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hb : ∀ i, i < varBound b → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
      simp [varBound, evalCircuit, iha ha, ihb hb]

theorem witness_from_assignment_recovers_eval
    (φ : Circuit)
    (σ : Assignment) :
    evalCircuit
        (assignmentOfWitness φ (fun i => σ i.val))
        φ =
      evalCircuit σ φ := by
  apply evalCircuit_eq_of_agree_below
  intro i hi
  simp [assignmentOfWitness, hi]

def SATWitnessAccepts
    (φ : Circuit)
    (w : SATWitness φ) : Prop :=
  IsCNF φ ∧
    evalCircuit (assignmentOfWitness φ w) φ = true

theorem satLanguage_iff_exists_finite_witness
    (φ : Circuit) :
    SATLanguage φ ↔
      ∃ w : SATWitness φ, SATWitnessAccepts φ w := by
  constructor
  · rintro ⟨hCNF, σ, hEval⟩
    let w : SATWitness φ := fun i => σ i.val
    refine ⟨w, hCNF, ?_⟩
    have hRecover := witness_from_assignment_recovers_eval φ σ
    simpa [w, hEval] using hRecover
  · rintro ⟨w, hCNF, hEval⟩
    exact ⟨hCNF, assignmentOfWitness φ w, hEval⟩

theorem encodeNat_length
    (n : Nat) :
    (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, ih]

theorem varBound_le_encoded_length
    (φ : Circuit) :
    varBound φ ≤ (encodeCircuit φ).length := by
  induction φ with
  | input i =>
      simp [varBound, encodeCircuit, encodeNat_length]
  | const b =>
      cases b <;> simp [varBound, encodeCircuit]
  | not c ih =>
      simp [varBound, encodeCircuit]
      omega
  | and a b iha ihb =>
      simp [varBound, encodeCircuit]
      omega
  | or a b iha ihb =>
      simp [varBound, encodeCircuit]
      omega

def witnessBits
    {φ : Circuit}
    (w : SATWitness φ) :
    BitString :=
  List.ofFn w

theorem witnessBits_length
    {φ : Circuit}
    (w : SATWitness φ) :
    (witnessBits w).length = varBound φ := by
  simp [witnessBits]

theorem witness_bits_linear_bound
    {φ : Circuit}
    (w : SATWitness φ) :
    (witnessBits w).length ≤ (encodeCircuit φ).length := by
  rw [witnessBits_length]
  exact varBound_le_encoded_length φ

#print axioms MCore.Real.CanonicalSATWitness.evalCircuit_eq_of_agree_below
#print axioms MCore.Real.CanonicalSATWitness.witness_from_assignment_recovers_eval
#print axioms MCore.Real.CanonicalSATWitness.satLanguage_iff_exists_finite_witness
#print axioms MCore.Real.CanonicalSATWitness.varBound_le_encoded_length
#print axioms MCore.Real.CanonicalSATWitness.witness_bits_linear_bound

end CanonicalSATWitness
end Real
end MCore
