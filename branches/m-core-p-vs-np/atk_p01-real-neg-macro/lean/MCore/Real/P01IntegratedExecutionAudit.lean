import MCore.Real.P01IntegratedExecutionMachine

namespace MCore
namespace Real
namespace P01IntegratedExecutionAudit

open P01FullVerifierPhysicalControl
open P01IntegratedMachine
open P01IntegratedExecutionMachine

theorem decoder_step :
    ∀ s : Option Bool,
      decoderEvaluatorMachine.transition decodeInstr s =
        (readWitness, s, .stay) := by
  intro s
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness]

theorem read_step :
    ∀ s : Option Bool,
      decoderEvaluatorMachine.transition readWitness s =
        (pushRes, s, .stay) := by
  intro s
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness, pushRes]

theorem push_step :
    ∀ s : Option Bool,
      decoderEvaluatorMachine.transition pushRes s =
        (decodeInstr, s, .stay) := by
  intro s
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    evalNeg, evalAnd, evalOr, pushRes]

theorem decoder_cycle_nonhalting :
    decoderEvaluatorMachine.halting decodeInstr = false ∧
    decoderEvaluatorMachine.halting readWitness = false ∧
    decoderEvaluatorMachine.halting pushRes = false := by
  decide

/-- The current local decoder/evaluator control has a concrete three-state
cycle and therefore is not itself the terminal physical verifier realization.
This closes the attempted promotion route negatively; it does not affect the
already-GREEN local scan/refinement lemmas. -/
theorem current_decoder_evaluator_not_terminal :
    ∀ s : Option Bool,
      (decoderEvaluatorMachine.transition decodeInstr s).1 = readWitness ∧
      (decoderEvaluatorMachine.transition readWitness s).1 = pushRes ∧
      (decoderEvaluatorMachine.transition pushRes s).1 = decodeInstr := by
  intro s
  simp [decoder_step, read_step, push_step]

#print axioms MCore.Real.P01IntegratedExecutionAudit.decoder_cycle_nonhalting
#print axioms MCore.Real.P01IntegratedExecutionAudit.current_decoder_evaluator_not_terminal

end P01IntegratedExecutionAudit
end Real
end MCore
