import Mathlib.Computability.PartrecCode
import MCore.Real.P02BitStringNatCoding

namespace MCore
namespace Real
namespace P02BoundedSemanticInput

open CanonicalFinalProof
open P02BitStringNatCoding

/-- Bounded halting domain at the distinguished input 0.
Unlike `(c.eval 0).Dom`, this is decidable because `evaln` is total. -/
def DomFuel (fuel : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∃ v : Nat, Nat.Partrec.Code.evaln fuel c 0 = some v

instance (fuel : Nat) (c : Nat.Partrec.Code) : Decidable (DomFuel fuel c) := by
  unfold DomFuel
  cases h : Nat.Partrec.Code.evaln fuel c 0 with
  | none =>
      exact isFalse (by
        intro hex
        rcases hex with ⟨v, hv⟩
        simp [h] at hv)
  | some v =>
      exact isTrue ⟨v, rfl⟩

/-- Bounded semantic observation.  Failure within the chosen fuel is represented
by the empty bitstring; no halting oracle is queried. -/
def selfInputFuel (fuel : Nat) (c : Nat.Partrec.Code) : BitString :=
  ((Nat.Partrec.Code.evaln fuel c 0).bind decodeBitsNat).getD []

theorem evaln_zero_computable (fuel : Nat) :
    Computable (fun c : Nat.Partrec.Code =>
      Nat.Partrec.Code.evaln fuel c 0) := by
  have hArgs :
      Primrec (fun c : Nat.Partrec.Code => ((fuel, c), 0)) :=
    Primrec.pair
      (Primrec.pair (Primrec.const fuel) Primrec.id)
      (Primrec.const 0)
  have hEval :
      Primrec (fun (a : (Nat × Nat.Partrec.Code) × Nat) =>
        Nat.Partrec.Code.evaln a.1.1 a.1.2 a.2) :=
    Nat.Partrec.Code.evaln_prim
  exact (hEval.comp hArgs).to_comp

theorem decodeBitsNat_computable :
    Computable decodeBitsNat := by
  simpa [decodeBitsNat] using
    (Primrec.decode (α := BitString)).to_comp

theorem selfInputFuelOption_computable (fuel : Nat) :
    Computable (fun c : Nat.Partrec.Code =>
      (Nat.Partrec.Code.evaln fuel c 0).bind decodeBitsNat) := by
  have hEval := evaln_zero_computable fuel
  have hDecodePair :
      Computable (fun p : Nat.Partrec.Code × Nat =>
        decodeBitsNat p.2) :=
    decodeBitsNat_computable.comp Computable.snd
  exact hEval.option_bind hDecodePair.to₂

theorem selfInputFuel_computable (fuel : Nat) :
    Computable (selfInputFuel fuel) := by
  have hOpt := selfInputFuelOption_computable fuel
  have hDefault :
      Computable (fun _ : Nat.Partrec.Code => ([] : BitString)) :=
    Computable.const []
  simpa [selfInputFuel] using hOpt.option_getD hDefault

/-- Soundness of bounded observation: any concrete value seen by evaln is also
a value of the true partial semantics. -/
theorem evaln_value_sound
    {fuel : Nat}
    {c : Nat.Partrec.Code}
    {v : Nat}
    (h : v ∈ Nat.Partrec.Code.evaln fuel c 0) :
    v ∈ c.eval 0 :=
  Nat.Partrec.Code.evaln_sound h

/-- Completeness is existential in the fuel: every terminating result appears
at some finite stage. -/
theorem eval_value_has_fuel
    {c : Nat.Partrec.Code}
    {v : Nat}
    (h : v ∈ c.eval 0) :
    ∃ fuel : Nat, v ∈ Nat.Partrec.Code.evaln fuel c 0 := by
  exact (Nat.Partrec.Code.evaln_complete).mp h

/-- Monotonicity of bounded observations. -/
theorem evaln_value_mono
    {fuel₁ fuel₂ : Nat}
    {c : Nat.Partrec.Code}
    {v : Nat}
    (hf : fuel₁ ≤ fuel₂)
    (h : v ∈ Nat.Partrec.Code.evaln fuel₁ c 0) :
    v ∈ Nat.Partrec.Code.evaln fuel₂ c 0 :=
  Nat.Partrec.Code.evaln_mono hf h

#print axioms MCore.Real.P02BoundedSemanticInput.evaln_zero_computable
#print axioms MCore.Real.P02BoundedSemanticInput.decodeBitsNat_computable
#print axioms MCore.Real.P02BoundedSemanticInput.selfInputFuel_computable
#print axioms MCore.Real.P02BoundedSemanticInput.evaln_value_sound
#print axioms MCore.Real.P02BoundedSemanticInput.eval_value_has_fuel
#print axioms MCore.Real.P02BoundedSemanticInput.evaln_value_mono

end P02BoundedSemanticInput
end Real
end MCore
