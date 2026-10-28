import MCore.Real.Semantics
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01VerifierGateMachine

namespace MCore
namespace Real
namespace P01FullVerifierStackSemantics

open CircuitK1
open CanonicalCircuitBits

/-- Finite instruction alphabet for bottom-up circuit evaluation.
The input index is data decoded from tape; it is not a machine-control state. -/
inductive EvalInstr where
  | input : Nat → EvalInstr
  | const : Bool → EvalInstr
  | neg : EvalInstr
  | and : EvalInstr
  | or : EvalInstr
  deriving DecidableEq, Repr

/-- Postorder evaluation program corresponding to the canonical prefix AST.
A fixed tape machine can obtain this effect by traversing the encoded source
and maintaining the value stack on tape. -/
def evalProgram : Circuit → List EvalInstr
  | .input i => [EvalInstr.input i]
  | .const b => [EvalInstr.const b]
  | .not c => evalProgram c ++ [EvalInstr.neg]
  | .and a b => evalProgram a ++ evalProgram b ++ [EvalInstr.and]
  | .or a b => evalProgram a ++ evalProgram b ++ [EvalInstr.or]

def execInstr (σ : Assignment) : List Bool → EvalInstr → Option (List Bool)
  | stack, .input i => some (σ i :: stack)
  | stack, .const b => some (b :: stack)
  | [], .neg => none
  | x :: xs, .neg => some ((!x) :: xs)
  | r :: l :: xs, .and => some (Bool.and l r :: xs)
  | _, .and => none
  | r :: l :: xs, .or => some (Bool.or l r :: xs)
  | _, .or => none

def runProgram (σ : Assignment) : List EvalInstr → List Bool → Option (List Bool)
  | [], stack => some stack
  | i :: is, stack => do
      let stack' ← execInstr σ stack i
      runProgram σ is stack'

theorem runProgram_append
    (σ : Assignment) (xs ys : List EvalInstr) (stack : List Bool) :
    runProgram σ (xs ++ ys) stack =
      (runProgram σ xs stack >>= runProgram σ ys) := by
  induction xs generalizing stack with
  | nil => rfl
  | cons x xs ih =>
      simp [runProgram]
      cases h : execInstr σ stack x with
      | none => simp [h]
      | some stack' =>
          simp [h, ih]

/-- Exact semantic invariant for the bottom-up stack evaluator. -/
theorem evalProgram_correct_aux
    (σ : Assignment) (c : Circuit) (stack : List Bool) :
    runProgram σ (evalProgram c) stack =
      some (evalCircuit σ c :: stack) := by
  induction c generalizing stack with
  | input i =>
      simp [evalProgram, runProgram, execInstr, evalCircuit]
  | const b =>
      simp [evalProgram, runProgram, execInstr, evalCircuit]
  | not c ih =>
      rw [evalProgram, runProgram_append, ih]
      simp [runProgram, execInstr, evalCircuit]
  | and a b iha ihb =>
      rw [evalProgram, List.append_assoc, runProgram_append, iha]
      simp
      rw [runProgram_append, ihb]
      simp [runProgram, execInstr, evalCircuit]
  | or a b iha ihb =>
      rw [evalProgram, List.append_assoc, runProgram_append, iha]
      simp
      rw [runProgram_append, ihb]
      simp [runProgram, execInstr, evalCircuit]

theorem evalProgram_correct
    (σ : Assignment) (c : Circuit) :
    runProgram σ (evalProgram c) [] = some [evalCircuit σ c] := by
  simpa using evalProgram_correct_aux σ c []

/-- Program length equals circuit size, giving a linear number of semantic
stack instructions before accounting for tape shuttling. -/
theorem evalProgram_length (c : Circuit) :
    (evalProgram c).length = CircuitK1.size c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih =>
      simp [evalProgram, CircuitK1.size, ih]
  | and a b iha ihb =>
      simp [evalProgram, CircuitK1.size, iha, ihb]
      omega
  | or a b iha ihb =>
      simp [evalProgram, CircuitK1.size, iha, ihb]
      omega

theorem evalProgram_length_le_encoding (c : Circuit) :
    (evalProgram c).length ≤ (encodeCircuit c).length := by
  rw [evalProgram_length]
  exact size_le_encodeCircuit_length c

#print axioms MCore.Real.P01FullVerifierStackSemantics.evalProgram_correct
#print axioms MCore.Real.P01FullVerifierStackSemantics.evalProgram_length_le_encoding

end P01FullVerifierStackSemantics
end Real
end MCore
