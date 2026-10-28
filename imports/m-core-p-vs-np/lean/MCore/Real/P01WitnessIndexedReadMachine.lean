import MCore.Real.P01WitnessIndexedRead

namespace MCore
namespace Real
namespace P01WitnessIndexedReadMachine

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead

/-!
Concrete fixed-control indexed witness reader.

Protocol:
* the head starts on unary `encodeNat i`;
* state 0 consumes one unary `true` marker;
* state 1 crosses blanks left and erases one witness cell;
* state 2 crosses blanks right back to the remaining unary index;
* when the unary `false` terminator is reached, state 3 crosses left to the
  first unconsumed witness cell;
* states 4/5 halt with true/false result respectively.

No value of `i` is stored in finite control.  Both counters are represented
physically by the unary input and the destructively consumed witness prefix.
-/
def witnessIndexedReadMachine : TM (Fin 6) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true  => (1, none, .left)
        | some false => (3, some false, .left)
        | none       => (5, none, .stay)
      else if q = 1 then
        match symbol with
        | none   => (1, none, .left)
        | some _ => (2, none, .right)
      else if q = 2 then
        match symbol with
        | none       => (2, none, .right)
        | some true  => (1, none, .left)
        | some false => (3, some false, .left)
      else if q = 3 then
        match symbol with
        | none       => (3, none, .left)
        | some true  => (4, some true, .stay)
        | some false => (5, some false, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 4) || (q == 5) }

@[simp] theorem witnessIndexedReadMachine_blank :
    witnessIndexedReadMachine.blank = none := rfl

@[simp] theorem witnessIndexedReadMachine_not_halt0 :
    witnessIndexedReadMachine.halting (0 : Fin 6) = false := by decide

@[simp] theorem witnessIndexedReadMachine_halt4 :
    witnessIndexedReadMachine.halting (4 : Fin 6) = true := by decide

@[simp] theorem witnessIndexedReadMachine_halt5 :
    witnessIndexedReadMachine.halting (5 : Fin 6) = true := by decide

def witnessIndexedAccepting (q : Fin 6) : Bool := q == 4

/-- Zero index is the first physical witness cell left of the delimiter. -/
theorem read_zero_false (tail : BitString) :
    (witnessIndexedReadMachine.run 3
      { state := witnessIndexedReadMachine.initial,
        tape := witnessReadTape (false :: tail) 0 }).state = (5 : Fin 6) := by
  simp [witnessReadTape, encodeNat, witnessIndexedReadMachine, TM.run, TM.step,
    Tape.write, Tape.move]

theorem read_zero_true (tail : BitString) :
    (witnessIndexedReadMachine.run 3
      { state := witnessIndexedReadMachine.initial,
        tape := witnessReadTape (true :: tail) 0 }).state = (4 : Fin 6) := by
  simp [witnessReadTape, encodeNat, witnessIndexedReadMachine, TM.run, TM.step,
    Tape.write, Tape.move]

/-- Conservative polynomial budget for repeated delimiter shuttling.
The universal correctness/halting induction will inhabit the certificate
against this fixed budget. -/
def witnessIndexedReadTimeBound : TimeBound :=
  fun n => 16 * (n + 1) ^ 2

theorem witnessIndexedReadTimeBound_poly :
    PolynomialTimeBound witnessIndexedReadTimeBound := by
  exact ⟨16, 2, fun n => Nat.le_refl _⟩

#print axioms MCore.Real.P01WitnessIndexedReadMachine.read_zero_false
#print axioms MCore.Real.P01WitnessIndexedReadMachine.read_zero_true
#print axioms MCore.Real.P01WitnessIndexedReadMachine.witnessIndexedReadTimeBound_poly

end P01WitnessIndexedReadMachine
end Real
end MCore
