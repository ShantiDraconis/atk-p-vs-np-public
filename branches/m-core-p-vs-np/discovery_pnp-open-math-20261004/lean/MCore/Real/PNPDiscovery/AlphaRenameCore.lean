import MCore.Real.Semantics

namespace MCore
namespace Real
namespace PNPDiscovery

open CircuitK1
open Semantics

def renameInputs (ρ : Nat → Nat) : Circuit → Circuit
  | .input i => .input (ρ i)
  | .const b => .const b
  | .not c => .not (renameInputs ρ c)
  | .and a b => .and (renameInputs ρ a) (renameInputs ρ b)
  | .or a b => .or (renameInputs ρ a) (renameInputs ρ b)

theorem evalCircuit_renameInputs
    (ρ : Nat → Nat)
    (σ : Assignment)
    (c : Circuit) :
    evalCircuit σ (renameInputs ρ c) =
      evalCircuit (fun i => σ (ρ i)) c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih => simp [renameInputs, evalCircuit, ih]
  | and a b iha ihb => simp [renameInputs, evalCircuit, iha, ihb]
  | or a b iha ihb => simp [renameInputs, evalCircuit, iha, ihb]

def HasLeftInverse (ρ : Nat → Nat) : Prop :=
  ∃ λ : Nat → Nat, ∀ i, λ (ρ i) = i

theorem leftInverse_injective
    (ρ : Nat → Nat)
    (h : HasLeftInverse ρ) :
    Function.Injective ρ := by
  rcases h with ⟨λ, hλ⟩
  intro i j hij
  have := congrArg λ hij
  simpa [hλ] using this

#print axioms MCore.Real.PNPDiscovery.evalCircuit_renameInputs
#print axioms MCore.Real.PNPDiscovery.leftInverse_injective

end PNPDiscovery
end Real
end MCore
