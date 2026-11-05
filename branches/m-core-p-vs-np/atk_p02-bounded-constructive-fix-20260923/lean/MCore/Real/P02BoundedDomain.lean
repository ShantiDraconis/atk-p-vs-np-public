import MCore.Real.P02BoundedSemanticInput
import MCore.CircuitK1

namespace MCore
namespace Real
namespace P02BoundedDomain

open CircuitK1
open P02BoundedSemanticInput

/-- Purely syntactic bounded circuit domain. -/
def DomSize (n : Nat) : Set Circuit :=
  { phi | CircuitK1.size phi ≤ n }

instance (n : Nat) : DecidablePred (fun phi : Circuit => phi ∈ DomSize n) := by
  intro phi
  change Decidable (CircuitK1.size phi ≤ n)
  infer_instance

@[simp] theorem mem_DomSize_iff
    (n : Nat) (phi : Circuit) :
    phi ∈ DomSize n ↔ CircuitK1.size phi ≤ n :=
  Iff.rfl

theorem mem_own_DomSize (phi : Circuit) :
    phi ∈ DomSize (CircuitK1.size phi) := by
  simp [DomSize]

/-- A code is bounded semantically by fuel exactly when evaln returns some
result at input zero.  This predicate is decidable without a halting oracle. -/
instance DomFuel_decidable
    (fuel : Nat) :
    DecidablePred (DomFuel fuel) := by
  intro c
  infer_instance

/-- Successful bounded evaluation remains successful at every larger fuel. -/
theorem DomFuel_mono
    {fuel₁ fuel₂ : Nat}
    (hFuel : fuel₁ ≤ fuel₂)
    {c : Nat.Partrec.Code}
    (h : DomFuel fuel₁ c) :
    DomFuel fuel₂ c := by
  rcases h with ⟨v, hv⟩
  exact ⟨v, Nat.Partrec.Code.evaln_mono hFuel hv⟩

#print axioms MCore.Real.P02BoundedDomain.mem_own_DomSize
#print axioms MCore.Real.P02BoundedDomain.DomFuel_mono

end P02BoundedDomain
end Real
end MCore
