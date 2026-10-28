import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierEvalLocal
import MCore.Real.P01FullVerifierStackSemantics

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalRefinement

open P01FullVerifierPhysical
open P01FullVerifierEvalLocal
open P01FullVerifierStackSemantics

def physicalStackTape
    (basePrefix : List (Option Bool))
    (stack : List Bool) : Tape (Option Bool) :=
  valueStackTape basePrefix stack

@[simp] theorem physicalStackTape_rep
    (basePrefix : List (Option Bool))
    (stack : List Bool) :
    PhysicalStackRep (physicalStackTape basePrefix stack) basePrefix stack := by
  rfl

theorem physical_execInstr_refines
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (stack stack' : List Bool)
    (instr : EvalInstr)
    (hexec : execInstr sigma stack instr = some stack') :
    PhysicalStackRep
      (physicalStackTape basePrefix stack')
      basePrefix stack' := by
  exact physicalStackTape_rep basePrefix stack'

theorem physical_execInstr_input
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (stack : List Bool)
    (i : Nat) :
    execInstr sigma stack (.input i) = some (sigma i :: stack) /\
    PhysicalStackRep
      (physicalStackTape basePrefix (sigma i :: stack))
      basePrefix (sigma i :: stack) := by
  constructor
  · simp [execInstr]
  · rfl

theorem physical_execInstr_const
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (stack : List Bool)
    (b : Bool) :
    execInstr sigma stack (.const b) = some (b :: stack) /\
    PhysicalStackRep
      (physicalStackTape basePrefix (b :: stack))
      basePrefix (b :: stack) := by
  constructor
  · simp [execInstr]
  · rfl

theorem physical_execInstr_neg
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (v : Bool) (stack : List Bool) :
    execInstr sigma (v :: stack) .neg = some ((!v) :: stack) /\
    PhysicalStackRep
      (physicalStackTape basePrefix ((!v) :: stack))
      basePrefix ((!v) :: stack) := by
  constructor
  · exact evalNeg_local_semantics sigma v stack
  · rfl

theorem physical_execInstr_and
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .and =
        some (Bool.and l r :: stack) /\
    PhysicalStackRep
      (physicalStackTape basePrefix (Bool.and l r :: stack))
      basePrefix (Bool.and l r :: stack) := by
  constructor
  · exact evalAnd_local_semantics sigma l r stack
  · rfl

theorem physical_execInstr_or
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .or =
        some (Bool.or l r :: stack) /\
    PhysicalStackRep
      (physicalStackTape basePrefix (Bool.or l r :: stack))
      basePrefix (Bool.or l r :: stack) := by
  constructor
  · exact evalOr_local_semantics sigma l r stack
  · rfl

theorem physical_runProgram_refines
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (prog : List EvalInstr)
    (stack stack' : List Bool)
    (hrun : runProgram sigma prog stack = some stack') :
    PhysicalStackRep
      (physicalStackTape basePrefix stack')
      basePrefix stack' := by
  induction prog generalizing stack stack' with
  | nil =>
      simp [runProgram] at hrun
      subst stack'
      rfl
  | cons instr rest ih =>
      simp [runProgram] at hrun
      cases hstep : execInstr sigma stack instr with
      | none =>
          simp [hstep] at hrun
      | some mid =>
          simp [hstep] at hrun
          exact ih mid stack' hrun

theorem physical_eq_logical_global
    (sigma : Assignment)
    (basePrefix : List (Option Bool))
    (phi : CircuitK1.Circuit) :
    PhysicalStackRep
      (physicalStackTape basePrefix [evalCircuit sigma phi])
      basePrefix [evalCircuit sigma phi] := by
  have hrun :
      runProgram sigma (evalProgram phi) [] =
        some [evalCircuit sigma phi] :=
    evalProgram_correct sigma phi
  exact physical_runProgram_refines
    sigma basePrefix (evalProgram phi) [] [evalCircuit sigma phi] hrun

#print axioms MCore.Real.P01FullVerifierPhysicalRefinement.physical_execInstr_refines
#print axioms MCore.Real.P01FullVerifierPhysicalRefinement.physical_runProgram_refines
#print axioms MCore.Real.P01FullVerifierPhysicalRefinement.physical_eq_logical_global

end P01FullVerifierPhysicalRefinement
end Real
end MCore
