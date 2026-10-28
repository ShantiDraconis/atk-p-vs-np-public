import MCore.Real.P01IntegratedMachine
import MCore.Real.P01PhysicalVerifierFoundations

namespace MCore
namespace Real
namespace P01IntegratedExecutionMachine

open CanonicalFinalProof
open CanonicalSATParserNTM
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalControl
open P01PhysicalVerifierFoundations
open P01IntegratedMachine

private def parserOfIntegrated (q : IntegratedState) (h : q.val < 25) : Fin 25 :=
  ⟨q.val, h⟩

private def witnessOfIntegrated
    (q : IntegratedState) (hlo : 25 ≤ q.val) (hhi : q.val < 37) : Fin 12 :=
  ⟨q.val - 25, by omega⟩

private def verifierOfIntegrated
    (q : IntegratedState) (hlo : 37 ≤ q.val) (hhi : q.val < 45) : Fin 8 :=
  ⟨q.val - 37, by omega⟩

private def liftParserChoice
    (c : Fin 25 × Option Bool × Direction) :
    IntegratedState × Option Bool × Direction :=
  (parserState c.1, c.2.1, c.2.2)

private def liftWitnessChoice
    (c : Fin 12 × Option Bool × Direction) :
    IntegratedState × Option Bool × Direction :=
  (witnessState c.1, c.2.1, c.2.2)

private def liftVerifierChoice
    (c : Fin 8 × Option Bool × Direction) :
    IntegratedState × Option Bool × Direction :=
  (verifierState c.1, c.2.1, c.2.2)

/-- Concrete fixed-control NTM joining the already-certified parser,
witness-preparation and physical-verifier control state spaces.  This file
constructs the machine only; its global halting and SATBits correctness are
proved separately. -/
def integratedExecutionMachine : NTM IntegratedState (Option Bool) :=
  { initial := parserState parserNTM.initial
    blank := none
    transition := fun q symbol =>
      if hp : q.val < 25 then
        let p := parserOfIntegrated q hp
        if parserNTM.accepting p then
          [(witnessState witnessPreservingPrep.initial, symbol, .stay)]
        else if parserNTM.rejecting p then
          [(integratedReject, symbol, .stay)]
        else
          (parserNTM.transition p symbol).map liftParserChoice
      else if hwlo : 25 ≤ q.val then
        if hwhi : q.val < 37 then
          let w := witnessOfIntegrated q hwlo hwhi
          if witnessPreservingPrep.accepting w then
            [(verifierState decoderEvaluatorMachine.initial, symbol, .stay)]
          else if witnessPreservingPrep.rejecting w then
            [(integratedReject, symbol, .stay)]
          else
            (witnessPreservingPrep.transition w symbol).map liftWitnessChoice
        else if hvlo : 37 ≤ q.val then
          if hvhi : q.val < 45 then
            let v := verifierOfIntegrated q hvlo hvhi
            if decoderEvaluatorMachine.halting v then
              if physicalResultAccept symbol then
                [(integratedAccept, symbol, .stay)]
              else
                [(integratedReject, symbol, .stay)]
            else
              [liftVerifierChoice (decoderEvaluatorMachine.transition v symbol)]
          else
            []
        else
          []
      else
        []
    accepting := fun q => q == integratedAccept
    rejecting := fun q => q == integratedReject }

@[simp] theorem integratedExecutionMachine_blank :
    integratedExecutionMachine.blank = none := rfl

@[simp] theorem integratedExecutionMachine_initial :
    integratedExecutionMachine.initial = parserState parserNTM.initial := rfl

@[simp] theorem integratedExecutionMachine_accept_terminal :
    integratedExecutionMachine.accepting integratedAccept = true := by
  simp [integratedExecutionMachine]

@[simp] theorem integratedExecutionMachine_reject_terminal :
    integratedExecutionMachine.rejecting integratedReject = true := by
  simp [integratedExecutionMachine]

theorem integratedExecutionMachine_fixed_type :
    Nonempty (NTM (Fin 47) (Option Bool)) :=
  ⟨integratedExecutionMachine⟩

#print axioms MCore.Real.P01IntegratedExecutionMachine.integratedExecutionMachine_blank
#print axioms MCore.Real.P01IntegratedExecutionMachine.integratedExecutionMachine_fixed_type

end P01IntegratedExecutionMachine
end Real
end MCore
