import MCore.Real.Model
import MCore.Real.Semantics

namespace MCore
namespace Real

open CircuitK1

namespace NTM

/-- A fixed machine decides a language within a supplied time bound, measured
    using the caller's input-size function. This reuses the repository NTM;
    it does not introduce a parallel machine model. -/
def DecidesWithin
    {State Symbol Input : Type}
    (machine : NTM State Symbol)
    (encode : Input → Configuration State Symbol)
    (inputSize : Input → Nat)
    (language : Input → Prop)
    (T : TimeBound) : Prop :=
  ∀ x : Input,
    machine.HaltsWithin (T (inputSize x)) (encode x) ∧
      (machine.AcceptsWithin (T (inputSize x)) (encode x) ↔ language x)

end NTM

/-- SAT over the existing Circuit AST and structural CNF predicate. -/
def SATLanguage (φ : Circuit) : Prop :=
  IsCNF φ ∧ ∃ σ : Assignment, evalCircuit σ φ = true

/-- Exact witness package still missing from the SAT-realization track.
    Supplying an inhabitant is scientific/formal content; this structure does
    not manufacture a machine or a runtime theorem. -/
structure SATMachineRealization where
  State : Type
  Symbol : Type
  machine : NTM State Symbol
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  /-- Encoding may write the input tape, but it may not smuggle input-dependent
      computation into the control state. Every run starts in machine.initial. -/
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  decides :
    NTM.DecidesWithin machine encode CircuitK1.size SATLanguage timeBound

/-- Any supplied realization exposes its exact fixed-time decision contract. -/
theorem satMachineRealization_starts_initial
    (R : SATMachineRealization)
    (φ : Circuit) :
    (R.encode φ).state = R.machine.initial :=
  R.encode_initial φ

#print axioms MCore.Real.satMachineRealization_starts_initial

theorem satMachineRealization_decides
    (R : SATMachineRealization) :
    NTM.DecidesWithin
      R.machine R.encode CircuitK1.size SATLanguage R.timeBound :=
  R.decides

/-- The current frontier is explicit existence of a realization witness. -/
def SATMachineFrontier : Prop :=
  Nonempty SATMachineRealization

#print axioms MCore.Real.satMachineRealization_decides

end Real
end MCore
