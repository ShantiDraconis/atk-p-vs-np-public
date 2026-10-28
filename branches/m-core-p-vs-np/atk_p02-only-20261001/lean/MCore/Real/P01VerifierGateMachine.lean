import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace P01VerifierGateMachine

open CanonicalFinalProof

/-- Two-input Boolean gate command.
false = AND, true = OR. -/
def gateEvalMachine : TM (Fin 9) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, none, .right)
        | some true  => (2, none, .right)
        | none       => (8, none, .stay)
      else if q = 1 then
        match symbol with
        | some false => (3, none, .right)
        | some true  => (4, none, .right)
        | none       => (8, none, .stay)
      else if q = 2 then
        match symbol with
        | some false => (5, none, .right)
        | some true  => (6, none, .right)
        | none       => (8, none, .stay)
      else if q = 3 then
        match symbol with
        | some _ => (7, some false, .stay)
        | none   => (8, none, .stay)
      else if q = 4 then
        match symbol with
        | some b => (7, some b, .stay)
        | none   => (8, none, .stay)
      else if q = 5 then
        match symbol with
        | some b => (7, some b, .stay)
        | none   => (8, none, .stay)
      else if q = 6 then
        match symbol with
        | some _ => (7, some true, .stay)
        | none   => (8, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 7) || (q == 8) }

@[simp] theorem gateEvalMachine_blank :
    gateEvalMachine.blank = none := rfl

def gateCommand (isOr a b : Bool) : BitString :=
  [isOr, a, b]

def gateResult (isOr a b : Bool) : Bool :=
  if isOr then Bool.or a b else Bool.and a b

/-- Three finite-control transitions evaluate one AND/OR gate exactly. -/
theorem gateEval_run
    (isOr a b : Bool) :
    let final :=
      gateEvalMachine.run 3
        (initialTMConfig gateEvalMachine (gateCommand isOr a b))
    final.state = (7 : Fin 9) ∧
      final.tape.head = some (gateResult isOr a b) := by
  cases isOr <;> cases a <;> cases b <;>
    simp [gateEvalMachine, gateCommand, gateResult, TM.run, TM.step,
      initialTMConfig, inputTape, Tape.write, Tape.move]

def gateEvalTimeBound : TimeBound := fun _ => 3

theorem gateEvalTimeBound_poly :
    PolynomialTimeBound gateEvalTimeBound := by
  refine ⟨3, 0, ?_⟩
  intro n
  simp [gateEvalTimeBound]

#print axioms MCore.Real.P01VerifierGateMachine.gateEval_run
#print axioms MCore.Real.P01VerifierGateMachine.gateEvalTimeBound_poly

end P01VerifierGateMachine
end Real
end MCore
