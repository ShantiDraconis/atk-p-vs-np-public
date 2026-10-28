import MCore.Real.CanonicalSATNatParserAttack

namespace MCore
namespace Real
namespace CanonicalSATVarPayloadMachine

open CanonicalFinalProof
open CanonicalCircuitBits

/--
Finite-control machine for the INPUT payload.
State 0 scans unary true bits.
State 1 is the successful halt after consuming the false terminator.
State 2 is the reject halt reached on blank before a terminator.

No variable index is stored in control.  The unary payload is validated
operationally and erased from the tape while the head advances.
-/
def varPayloadMachine : TM (Fin 3) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true  => (0, none, .right)
        | some false => (1, none, .right)
        | none       => (2, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 1) || (q == 2) }

def varConfig
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 3) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem varConfig_state
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    (varConfig q left bits).state = q := by
  cases bits <;> rfl

@[simp] theorem varPayloadMachine_not_halted_zero :
    varPayloadMachine.halting (0 : Fin 3) = false := by
  decide

@[simp] theorem varPayloadMachine_halted_one :
    varPayloadMachine.halting (1 : Fin 3) = true := by
  decide

@[simp] theorem varPayloadMachine_halted_two :
    varPayloadMachine.halting (2 : Fin 3) = true := by
  decide

theorem var_step_true
    (left : List (Option Bool))
    (rest : BitString) :
    varPayloadMachine.step (varConfig 0 left (true :: rest)) =
      varConfig 0 (none :: left) rest := by
  cases rest <;>
    simp [varPayloadMachine, varConfig, TM.step, Tape.write, Tape.move]

theorem var_step_false
    (left : List (Option Bool))
    (rest : BitString) :
    varPayloadMachine.step (varConfig 0 left (false :: rest)) =
      varConfig 1 (none :: left) rest := by
  cases rest <;>
    simp [varPayloadMachine, varConfig, TM.step, Tape.write, Tape.move]

theorem var_step_blank_rejects
    (left : List (Option Bool)) :
    varPayloadMachine.step (varConfig 0 left []) =
      varConfig 2 left [] := by
  simp [varPayloadMachine, varConfig, TM.step, Tape.write, Tape.move]

/--
Running on encodeNat n consumes exactly n unary true cells plus the false
terminator and halts with the head on the untouched tail.
-/
theorem replicate_none_append_cons
    (n : Nat)
    (left : List (Option Bool)) :
    List.replicate n none ++ none :: left =
      none :: List.replicate n none ++ left := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, ih, List.append_assoc]

theorem var_run_encodeNat
    (left : List (Option Bool))
    (n : Nat)
    (tail : BitString) :
    varPayloadMachine.run (n + 1)
      (varConfig 0 left (encodeNat n ++ tail)) =
    varConfig 1 (List.replicate (n + 1) none ++ left) tail := by
  induction n generalizing left with
  | zero =>
      simp only [encodeNat, List.cons_append, Nat.zero_add]
      rw [TM.run, varConfig_state, varPayloadMachine_not_halted_zero]
      rw [var_step_false]
      simp [TM.run, varConfig, List.replicate_succ]
  | succ n ih =>
      simp only [encodeNat, List.cons_append]
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [TM.run, varConfig_state, varPayloadMachine_not_halted_zero]
      rw [var_step_true]
      rw [ih (none :: left)]
      apply congrArg (fun xs => varConfig 1 xs tail)
      simp only [Nat.succ_eq_add_one, Nat.add_assoc, List.replicate_succ]
      exact congrArg (fun xs => none :: xs)
        (replicate_none_append_cons n left)

theorem var_payload_halts_on_encodeNat
    (n : Nat)
    (tail : BitString) :
    varPayloadMachine.HaltsWithin (n + 1)
      (varConfig 0 [] (encodeNat n ++ tail)) := by
  rw [TM.HaltsWithin]
  rw [var_run_encodeNat]
  rw [varConfig_state]
  exact varPayloadMachine_halted_one

/--
The operational postcondition is stronger than mere halting: after success,
the unread suffix is exactly the original tail and every consumed payload cell
has been replaced by blank.
-/
theorem var_payload_success_postcondition
    (n : Nat)
    (tail : BitString) :
    let final :=
      varPayloadMachine.run (n + 1)
        (varConfig 0 [] (encodeNat n ++ tail))
    final.state = (1 : Fin 3) ∧
      final.tape.left = List.replicate (n + 1) none ∧
      (match tail with
       | [] => final.tape.head = none ∧ final.tape.right = []
       | b :: bs =>
           final.tape.head = some b ∧ final.tape.right = bs.map some) := by
  rw [var_run_encodeNat]
  cases tail <;> simp [varConfig]

/-- Empty/truncated payload reaches the reject state in one step. -/
theorem var_payload_blank_rejects :
    (varPayloadMachine.run 1 (varConfig 0 [] [])).state = (2 : Fin 3) := by
  rw [TM.run, varConfig_state, varPayloadMachine_not_halted_zero]
  rw [var_step_blank_rejects]
  simp [TM.run, varConfig]

/-- Constant linear bound for this submachine family. -/
def varPayloadTimeBound : TimeBound := fun n => n + 1

theorem varPayloadTimeBound_poly :
    PolynomialTimeBound varPayloadTimeBound := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [varPayloadTimeBound]

#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_step_true
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_step_false
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_run_encodeNat
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_payload_halts_on_encodeNat
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_payload_success_postcondition
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.var_payload_blank_rejects
#print axioms MCore.Real.CanonicalSATVarPayloadMachine.varPayloadTimeBound_poly

end CanonicalSATVarPayloadMachine
end Real
end MCore
