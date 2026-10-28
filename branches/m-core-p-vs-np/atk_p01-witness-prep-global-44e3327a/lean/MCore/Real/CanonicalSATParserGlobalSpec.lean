import MCore.Real.CanonicalSATParserLeafSourceProof
import MCore.Real.CanonicalSATSlotParserSpec
import MCore.Real.CanonicalSATSlotLog

namespace MCore
namespace Real
namespace CanonicalSATParserGlobalSpec

open CanonicalFinalProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog

/-- Log-aware form of the canonical prefix parser.  This is the exact abstract
recurrence implemented by the physical work-log protocol: a unary node keeps
the active-slot log, a binary node pushes one active slot, and a leaf pops the
rightmost active slot. -/
def logParseCore : Nat → SlotLog → BitString → Bool
  | 0, _, _ => false
  | fuel + 1, log, bits =>
      if activeSlots log = 0 then
        bits.isEmpty
      else
        match parseHead bits with
        | none => false
        | some (head, rest) =>
            match head with
            | .input _ =>
                match popSlot log with
                | none => false
                | some log' => logParseCore fuel log' rest
            | .const _ =>
                match popSlot log with
                | none => false
                | some log' => logParseCore fuel log' rest
            | .not =>
                logParseCore fuel log rest
            | .and =>
                logParseCore fuel (pushSlot log) rest
            | .or =>
                logParseCore fuel (pushSlot log) rest

/-- The physical tombstone log is semantically invisible: only its active-slot
count matters.  Hence the log-aware recurrence is definitionally equivalent to
the already-certified scalar slot parser. -/
theorem logParseCore_eq_slotParseCore
    (fuel : Nat)
    (log : SlotLog)
    (bits : BitString) :
    logParseCore fuel log bits =
      slotParseCore fuel (activeSlots log) bits := by
  induction fuel generalizing log bits with
  | zero =>
      simp [logParseCore, slotParseCore]
  | succ fuel ih =>
      cases hcount : activeSlots log with
      | zero =>
          simp [logParseCore, slotParseCore, hcount]
      | succ slots =>
          have hactive : activeSlots log ≠ 0 := by
            simp [hcount]
          cases hhead : parseHead bits with
          | none =>
              simp [logParseCore, slotParseCore, hcount, hhead]
          | some p =>
              rcases p with ⟨head, rest⟩
              cases head with
              | input i =>
                  cases hpop : popSlot log with
                  | none =>
                      have hz : activeSlots log = 0 :=
                        (popSlot_none_iff log).mp hpop
                      exact False.elim (hactive hz)
                  | some log' =>
                      have hdrop :=
                        activeSlots_popSlot log log' hpop
                      have hlog' : activeSlots log' = slots := by
                        rw [hcount] at hdrop
                        omega
                      simp [logParseCore, slotParseCore, hcount, hhead, hpop,
                        Head.arity, ih, hlog']
              | const b =>
                  cases hpop : popSlot log with
                  | none =>
                      have hz : activeSlots log = 0 :=
                        (popSlot_none_iff log).mp hpop
                      exact False.elim (hactive hz)
                  | some log' =>
                      have hdrop :=
                        activeSlots_popSlot log log' hpop
                      have hlog' : activeSlots log' = slots := by
                        rw [hcount] at hdrop
                        omega
                      simp [logParseCore, slotParseCore, hcount, hhead, hpop,
                        Head.arity, ih, hlog']
              | not =>
                  simp [logParseCore, slotParseCore, hcount, hhead,
                    Head.arity, ih]
              | and =>
                  have hpush :
                      activeSlots (pushSlot log) = Nat.succ (Nat.succ slots) := by
                    rw [activeSlots_pushSlot, hcount]
                  simp [logParseCore, slotParseCore, hcount, hhead,
                    Head.arity, ih, hpush]
              | or =>
                  have hpush :
                      activeSlots (pushSlot log) = Nat.succ (Nat.succ slots) := by
                    rw [activeSlots_pushSlot, hcount]
                  simp [logParseCore, slotParseCore, hcount, hhead,
                    Head.arity, ih, hpush]

@[simp] theorem logParseCore_initial
    (fuel : Nat)
    (bits : BitString) :
    logParseCore fuel initialSlotLog bits =
      slotParseCore fuel 1 bits := by
  simpa using
    logParseCore_eq_slotParseCore fuel initialSlotLog bits

theorem logAccept_iff_slotAccept
    (bits : BitString) :
    logParseCore (bits.length + 1) initialSlotLog bits = true ↔
      slotAccept bits = true := by
  simp [slotAccept, logParseCore_initial]

#print axioms MCore.Real.CanonicalSATParserGlobalSpec.logParseCore_eq_slotParseCore
#print axioms MCore.Real.CanonicalSATParserGlobalSpec.logAccept_iff_slotAccept

end CanonicalSATParserGlobalSpec
end Real
end MCore
