import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.P01VerifierGateMachine

namespace MCore
namespace Real
namespace P01FullVerifierEvalLocal

open P01FullVerifierPhysical
open P01FullVerifierStackSemantics
open P01VerifierGateMachine

theorem evalNeg_local_semantics
    (sigma : Assignment) (v : Bool) (stack : List Bool) :
    execInstr sigma (v :: stack) .neg = some ((!v) :: stack) := by
  simp [execInstr]

theorem evalAnd_local_semantics
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .and =
      some (Bool.and l r :: stack) := by
  rfl

theorem evalOr_local_semantics
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .or =
      some (Bool.or l r :: stack) := by
  rfl

theorem gate_and_exact (l r : Bool) :
    gateResult false l r = Bool.and l r := by
  rfl

theorem gate_or_exact (l r : Bool) :
    gateResult true l r = Bool.or l r := by
  rfl

#print axioms MCore.Real.P01FullVerifierEvalLocal.evalNeg_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.evalAnd_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.evalOr_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.gate_and_exact
#print axioms MCore.Real.P01FullVerifierEvalLocal.gate_or_exact

end P01FullVerifierEvalLocal
end Real
end MCore
