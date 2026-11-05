import MCore.Real.CanonicalSATParserLeafSourceProof
import MCore.Real.CanonicalSATParserReturnProof

namespace MCore
namespace Real
namespace CanonicalSATParserTerminalBranches

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserReturnProof

/-- Rejecting terminal configuration when state 16 discovers residual source
after the final active slot has already been consumed. -/
def leafResidualRejectConfig
    (pad : Nat)
    (last : Bool)
    (rest : BitString)
    (right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 24
    tape :=
      { left := rest.map some ++ List.replicate pad none
        head := some last
        right := none :: right } }

/-- If the slot log is exhausted but unread source remains, state 16 rejects
in exactly one transition. -/
theorem leaf16_residual_rejects
    (pad : Nat)
    (last : Bool)
    (rest : BitString)
    (right : List (Option Bool)) :
    parserMachine.step
        (leafSourceCheckConfig 16
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          right) =
      leafResidualRejectConfig pad last rest right := by
  simp [leafSourceCheckConfig, leafResidualRejectConfig, parserMachine,
    TM.step, Tape.write, Tape.move, List.append_assoc]

@[simp] theorem leafResidualRejectConfig_halted
    (pad : Nat)
    (last : Bool)
    (rest : BitString)
    (right : List (Option Bool)) :
    parserMachine.halting
      (leafResidualRejectConfig pad last rest right).state = true := by
  simp [leafResidualRejectConfig, parserMachine]

/-- Binary constructors require unread source because they increase the number
of outstanding slots. If the source is exhausted at state 20/21, the machine
reaches the canonical reject configuration in two transitions. -/
theorem binary_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (right : List (Option Bool)) :
    parserMachine.run 2
        (binaryReturnConfig []
          (List.replicate pad (none : Option Bool))
          right) =
      leafRejectConfig pad right := by
  cases pad with
  | zero => omega
  | succ p =>
      simp [TM.run, binaryReturnConfig, binaryCheckConfig,
        leafRejectConfig, parserMachine, TM.step, Tape.write, Tape.move,
        List.replicate_succ]

#print axioms MCore.Real.CanonicalSATParserTerminalBranches.leaf16_residual_rejects
#print axioms MCore.Real.CanonicalSATParserTerminalBranches.leafResidualRejectConfig_halted
#print axioms MCore.Real.CanonicalSATParserTerminalBranches.binary_exhausted_rejects

end CanonicalSATParserTerminalBranches
end Real
end MCore
