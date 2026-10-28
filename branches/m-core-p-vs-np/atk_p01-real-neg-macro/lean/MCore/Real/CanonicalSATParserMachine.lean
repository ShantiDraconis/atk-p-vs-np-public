import MCore.Real.CanonicalSATSlotLog
import MCore.Real.CanonicalSATSlotParserSpec

namespace MCore
namespace Real
namespace CanonicalSATParserMachine

open CanonicalFinalProof

/--
Canonical single-tape parser with constant finite control.

State map (Fin 25):
0 INIT_SCAN_RIGHT
1 INIT_WRITE_SLOT
2 INIT_CROSS_LEFT
3 INIT_REWIND
4 TAG_0
5 TAG_AFTER_0
6 TAG_AFTER_1
7 TAG_AFTER_00
8 TAG_AFTER_01
9 TAG_AFTER_10
10 VAR_LOOP
11 LEAF_SEEK_DELIMITER
12 LEAF_SCAN_LOG_RIGHT
13 LEAF_POP_RIGHTMOST_ACTIVE
14 LEAF_SCAN_REMAINING_NO_ACTIVE
15 LEAF_SCAN_REMAINING_ACTIVE
16 LEAF_CHECK_UNREAD_NO_ACTIVE
17 LEAF_CHECK_UNREAD_ACTIVE
18 BINARY_SEEK_DELIMITER
19 BINARY_SCAN_LOG_RIGHT
20 BINARY_RETURN_LOG_LEFT
21 BINARY_CHECK_UNREAD
22 REWIND_UNREAD_LEFT
23 ACCEPT
24 REJECT

Invariant used to simplify the work log:
* TAG_0 is entered only with at least one active slot.
* NOT consumes one slot and opens one slot: the work log is unchanged.
* AND/OR consume one slot and open two: net effect is push one active slot.
* leaves consume one slot: pop the rightmost active slot.

Thus only leaf needs an actual pop search.  This is equivalent to the slot
recurrence slots' = slots - 1 + arity while avoiding unnecessary pop+push
cycles for unary/binary constructors.
-/
def parserMachine : TM (Fin 25) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, none, .right)
      else if q = 1 then
        (2, some true, .left)
      else if q = 2 then
        (3, symbol, .left)
      else if q = 3 then
        match symbol with
        | some b => (3, some b, .left)
        | none => (4, none, .right)
      else if q = 4 then
        match symbol with
        | some false => (5, none, .right)
        | some true => (6, none, .right)
        | none => (24, none, .stay)
      else if q = 5 then
        match symbol with
        | some false => (7, none, .right)
        | some true => (8, none, .right)
        | none => (24, none, .stay)
      else if q = 6 then
        match symbol with
        | some false => (9, none, .right)
        | some true => (24, none, .stay)
        | none => (24, none, .stay)
      else if q = 7 then
        match symbol with
        | some false => (10, none, .right)
        | some true => (11, none, .right)
        | none => (24, none, .stay)
      else if q = 8 then
        match symbol with
        | some false => (11, none, .right)
        | some true => (4, none, .right)
        | none => (24, none, .stay)
      else if q = 9 then
        match symbol with
        | some _ => (18, none, .right)
        | none => (24, none, .stay)
      else if q = 10 then
        match symbol with
        | some true => (10, none, .right)
        | some false => (11, none, .right)
        | none => (24, none, .stay)
      else if q = 11 then
        match symbol with
        | some b => (11, some b, .right)
        | none => (12, none, .right)
      else if q = 12 then
        match symbol with
        | some b => (12, some b, .right)
        | none => (13, none, .left)
      else if q = 13 then
        match symbol with
        | some false => (13, some false, .left)
        | some true => (14, some false, .left)
        | none => (24, none, .stay)
      else if q = 14 then
        match symbol with
        | some false => (14, some false, .left)
        | some true => (15, some true, .left)
        | none => (16, none, .left)
      else if q = 15 then
        match symbol with
        | some _ => (15, symbol, .left)
        | none => (17, none, .left)
      else if q = 16 then
        match symbol with
        | none => (23, none, .stay)
        | some b => (24, some b, .stay)
      else if q = 17 then
        match symbol with
        | none => (24, none, .stay)
        | some b => (22, some b, .left)
      else if q = 18 then
        match symbol with
        | some b => (18, some b, .right)
        | none => (19, none, .right)
      else if q = 19 then
        match symbol with
        | some b => (19, some b, .right)
        | none => (20, some true, .left)
      else if q = 20 then
        match symbol with
        | some b => (20, some b, .left)
        | none => (21, none, .left)
      else if q = 21 then
        match symbol with
        | none => (24, none, .stay)
        | some b => (22, some b, .left)
      else if q = 22 then
        match symbol with
        | some b => (22, some b, .left)
        | none => (4, none, .right)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 23) || (q == 24) }

@[simp] theorem parserMachine_blank_none :
    parserMachine.blank = none := rfl

def parserAccepting : Fin 25 → Bool :=
  fun q => q == 23

@[simp] theorem parserAccepting_accept :
    parserAccepting (23 : Fin 25) = true := by decide

@[simp] theorem parserAccepting_reject :
    parserAccepting (24 : Fin 25) = false := by decide

@[simp] theorem parserMachine_halts_accept :
    parserMachine.halting (23 : Fin 25) = true := by decide

@[simp] theorem parserMachine_halts_reject :
    parserMachine.halting (24 : Fin 25) = true := by decide

def parserTimeBound : TimeBound :=
  fun n => 256 * (n + 1) ^ 2

theorem parserTimeBound_poly :
    PolynomialTimeBound parserTimeBound := by
  exact ⟨256, 2, fun n => Nat.le_refl (256 * (n + 1) ^ 2)⟩

theorem parserMachine_has_canonical_type :
    Nonempty (TM (Fin 25) (Option Bool)) :=
  ⟨parserMachine⟩

def parserStateCount : Nat := 24

theorem parserStateType :
    Fin (parserStateCount + 1) = Fin 25 := by
  rfl

def parserInitialConfig (bits : BitString) :
    Configuration (Fin 25) (Option Bool) :=
  initialTMConfig parserMachine bits

@[simp] theorem parserInitialConfig_state (bits : BitString) :
    (parserInitialConfig bits).state = (0 : Fin 25) := by
  rfl

#print axioms MCore.Real.CanonicalSATParserMachine.parserMachine_blank_none
#print axioms MCore.Real.CanonicalSATParserMachine.parserTimeBound_poly
#print axioms MCore.Real.CanonicalSATParserMachine.parserMachine_has_canonical_type
#print axioms MCore.Real.CanonicalSATParserMachine.parserInitialConfig_state

end CanonicalSATParserMachine
end Real
end MCore
