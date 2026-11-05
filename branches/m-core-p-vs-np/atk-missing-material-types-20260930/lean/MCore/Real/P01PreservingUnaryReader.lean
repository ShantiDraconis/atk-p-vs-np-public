import MCore.Real.P01MissingMaterialTypes
import MCore.Real.P01EvalCursorMachine

namespace MCore
namespace Real
namespace P01PreservingUnaryReader

open CanonicalFinalProof
open P01EvalCursorMachine

/-!
Fixed-control preserving unary witness reader, first material implementation.

Design invariant:
* the source unary counter is tape data, never finite-control data;
* the unique source/witness blank delimiter is moved through the witness by
  reversible adjacent swaps;
* the Boolean crossed by a swap is held only in finite control;
* after the selected bit is classified, the delimiter is walked back to its
  canonical position, restoring the witness byte-for-byte.

This file introduces the concrete control graph.  The global run theorem is
the next proof obligation; no inhabitant of PreservingUnaryWitnessReadGap is
claimed here.
-/

inductive PreserveReadState where
  | seekSource        -- seek first unread source bit from stack end
  | skipTag0          -- consume first 0
  | skipTag1          -- consume second 0
  | skipTag2          -- consume third 0
  | unary             -- inspect next unary marker
  | toDelimiter       -- move left to source/witness separator
  | crossFalse        -- separator swap, remembering false
  | crossTrue         -- separator swap, remembering true
  | backToUnary       -- return to unary counter
  | selected          -- unary terminator reached; seek selected witness bit
  | selectedFalse     -- selected witness value stored in control
  | selectedTrue
  | restoreSeek       -- seek moved witness prefix / movable delimiter
  | restoreFalse      -- reverse one delimiter swap, remembering false
  | restoreTrue       -- reverse one delimiter swap, remembering true
  | restoreReturnFalse
  | restoreReturnTrue
  | haltFalse
  | haltTrue
  | reject
  deriving DecidableEq, Repr

/-- Result carried only by terminal control states. -/
def result : PreserveReadState → Option Bool
  | .haltFalse => some false
  | .haltTrue => some true
  | _ => none

/-- Fixed finite-control transition graph.
The global tape invariant/proof is intentionally separate from this executable
control definition. -/
def preservingUnaryReader : TM PreserveReadState (Option Bool) :=
  { initial := .seekSource
    blank := none
    transition := fun q s =>
      match q with
      | .seekSource =>
          match s with
          | none => (.seekSource, none, .left)
          | some false => (.skipTag0, none, .right)
          | some true => (.reject, some true, .stay)
      | .skipTag0 =>
          match s with
          | some false => (.skipTag1, none, .right)
          | _ => (.reject, s, .stay)
      | .skipTag1 =>
          match s with
          | some false => (.skipTag2, none, .right)
          | _ => (.reject, s, .stay)
      | .skipTag2 => (.unary, s, .stay)
      | .unary =>
          match s with
          | some true => (.toDelimiter, none, .left)
          | some false => (.selected, none, .left)
          | none => (.reject, none, .stay)
      | .toDelimiter =>
          match s with
          | none => (.toDelimiter, none, .left)
          | some false => (.crossFalse, none, .left)
          | some true => (.crossTrue, none, .left)
      | .crossFalse =>
          match s with
          | none => (.backToUnary, some false, .right)
          | _ => (.reject, s, .stay)
      | .crossTrue =>
          match s with
          | none => (.backToUnary, some true, .right)
          | _ => (.reject, s, .stay)
      | .backToUnary =>
          match s with
          | none => (.backToUnary, none, .right)
          | some true => (.unary, some true, .stay)
          | some false => (.unary, some false, .stay)
      | .selected =>
          match s with
          | none => (.selected, none, .left)
          | some false => (.selectedFalse, some false, .stay)
          | some true => (.selectedTrue, some true, .stay)
      | .selectedFalse => (.restoreSeek, s, .right)
      | .selectedTrue => (.restoreSeek, s, .right)
      | .restoreSeek =>
          match s with
          | none => (.restoreSeek, none, .right)
          | some false => (.restoreFalse, none, .right)
          | some true => (.restoreTrue, none, .right)
      | .restoreFalse =>
          match s with
          | none => (.restoreReturnFalse, some false, .left)
          | _ => (.restoreSeek, s, .right)
      | .restoreTrue =>
          match s with
          | none => (.restoreReturnTrue, some true, .left)
          | _ => (.restoreSeek, s, .right)
      | .restoreReturnFalse =>
          match s with
          | none => (.haltFalse, none, .stay)
          | _ => (.restoreSeek, s, .right)
      | .restoreReturnTrue =>
          match s with
          | none => (.haltTrue, none, .stay)
          | _ => (.restoreSeek, s, .right)
      | .haltFalse => (.haltFalse, s, .stay)
      | .haltTrue => (.haltTrue, s, .stay)
      | .reject => (.reject, s, .stay)
    halting := fun q =>
      match q with
      | .haltFalse | .haltTrue | .reject => true
      | _ => false }

@[simp] theorem preservingUnaryReader_blank :
    preservingUnaryReader.blank = none := rfl

@[simp] theorem preservingUnaryReader_result_false :
    result .haltFalse = some false := rfl

@[simp] theorem preservingUnaryReader_result_true :
    result .haltTrue = some true := rfl

/-- Conservative polynomial envelope for repeated full-width shuttles.
The exact run proof may later tighten this without changing the interface. -/
def preservingUnaryReadTimeBound : TimeBound :=
  fun n => 128 * (n + 1) ^ 3

theorem preservingUnaryReadTimeBound_poly :
    PolynomialTimeBound preservingUnaryReadTimeBound := by
  exact ⟨128, 3, fun n => Nat.le_refl _⟩

#print axioms MCore.Real.P01PreservingUnaryReader.preservingUnaryReadTimeBound_poly

end P01PreservingUnaryReader
end Real
end MCore
