import MCore.Real.P01PreservingUnaryWitnessMarker
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01InputNodePreservingPlan

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01PreservingUnaryWitnessMarker

/-!
# Input-node preserving plan

This file connects the exact semantic input-node transition with the reversible
physical marker primitive.

The representation separates the already traversed witness pref from the
remaining suffix.  Moving the marker one cell to the right changes only where
the unique marker blank sits; the Boolean payload is unchanged.  Rewinding
performs the inverse transformation.

The remaining implementation obligation after this module is deliberately
narrow: a fixed-control unary driver/shuttle must invoke the local marker
advance once for each `true` of `encodeNat i`, observe the selected cell at
the `false` terminator, and invoke the inverse moves while consuming/restoring
the unary counter as required by the evaluator layout.
-/

/-- Physical local witness view.  `pref` is in logical left-to-right order;
because Tape.left stores nearest cells first, it appears reversed physically. -/
def witnessMarkerLayout
    (outerLeft : List (Option Bool))
    (pref suffix : BitString)
    (outerRight : List (Option Bool)) : Tape (Option Bool) :=
  { left := pref.reverse.map some ++ outerLeft
    head := none
    right := suffix.map some ++ outerRight }

@[simp] theorem witnessMarkerLayout_zero
    (outerLeft : List (Option Bool))
    (witness : BitString)
    (outerRight : List (Option Bool)) :
    witnessMarkerLayout outerLeft [] witness outerRight =
      { left := outerLeft
        head := none
        right := witness.map some ++ outerRight } := by
  simp [witnessMarkerLayout]

/-- One physical marker advance extends the traversed pref by exactly one
witness bit. -/
theorem markerAdvance_layout
    (outerLeft : List (Option Bool))
    (pref : BitString)
    (b : Bool) (suffix : BitString)
    (outerRight : List (Option Bool)) :
    markerAdvanceMachine.run 3
      { state := markerAdvanceMachine.initial
        tape :=
          witnessMarkerLayout outerLeft pref (b :: suffix) outerRight } =
      { state := .halt
        tape :=
          witnessMarkerLayout outerLeft (pref ++ [b]) suffix outerRight } := by
  have h :=
    markerAdvance_run_three
      (pref.reverse.map some ++ outerLeft) b
      (suffix.map some ++ outerRight)
  simpa [witnessMarkerLayout, markerBefore, markerAfter,
    List.reverse_append, List.map_append, List.append_assoc] using h

/-- One physical rewind removes exactly the last traversed witness bit from the
pref and restores the marker immediately before it. -/
theorem markerRewind_layout
    (outerLeft : List (Option Bool))
    (pref : BitString)
    (b : Bool) (suffix : BitString)
    (outerRight : List (Option Bool)) :
    markerRewindMachine.run 3
      { state := markerRewindMachine.initial
        tape :=
          witnessMarkerLayout outerLeft (pref ++ [b]) suffix outerRight } =
      { state := .halt
        tape :=
          witnessMarkerLayout outerLeft pref (b :: suffix) outerRight } := by
  have h :=
    markerRewind_run_three
      (pref.reverse.map some ++ outerLeft) b
      (suffix.map some ++ outerRight)
  simpa [witnessMarkerLayout, markerBefore, markerAfter,
    List.reverse_append, List.map_append, List.append_assoc] using h

/-- Kernel-level conservation law: the logical Boolean witness represented on
both sides of the marker is always exactly pref ++ suffix. -/
def witnessPayload (pref suffix : BitString) : BitString :=
  pref ++ suffix

theorem witnessPayload_advance
    (pref : BitString) (b : Bool) (suffix : BitString) :
    witnessPayload pref (b :: suffix) =
      witnessPayload (pref ++ [b]) suffix := by
  simp [witnessPayload, List.append_assoc]

theorem witnessPayload_rewind
    (pref : BitString) (b : Bool) (suffix : BitString) :
    witnessPayload (pref ++ [b]) suffix =
      witnessPayload pref (b :: suffix) :=
  (witnessPayload_advance pref b suffix).symm

/-- The semantic half of the sole missing evalStep input case.  The unary index
is decoded from tape data, and the unread tail is preserved exactly. -/
theorem evalStep_input_encoded
    (sigma : Assignment)
    (i : Nat)
    (rest : BitString)
    (frames : List EvalFrame) :
    evalStep sigma
      (needExpr
        (false :: false :: false :: (encodeNat i ++ rest))
        frames) =
      some (haveValue (sigma i) rest frames) := by
  simp [evalStep, needExpr, haveValue, decodeNat_encodeNat_append]

/-- A decomposition of a valid witness index gives the exact selected Boolean
as the first cell of the remaining suffix after i marker advances.  This is the
logical shape the unary physical driver must realize. -/
theorem witness_index_decomposition
    (witness : BitString) (i : Nat)
    (h : i < witness.length) :
    ∃ pref b suffix,
      witness = pref ++ b :: suffix ∧
      pref.length = i ∧
      witness.getD i false = b := by
  induction witness generalizing i with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases i with
      | zero =>
          refine ⟨[], head, tail, ?_, ?_, ?_⟩
          · simp
          · simp
          · simp [List.getD_cons_zero]
      | succ i =>
          have hi : i < tail.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          obtain ⟨pref, b, suffix, hsplit, hlen, hget⟩ :=
            ih i hi
          refine ⟨head :: pref, b, suffix, ?_, ?_, ?_⟩
          · simp [hsplit, List.append_assoc]
          · simp [hlen]
          · simpa [List.getD_cons_succ] using hget

/-- Consequently, moving a marker through exactly the decomposition pref
does not change the represented witness and positions the marker immediately
before the selected bit.  This theorem is representation-level; the per-cell
physical realization is markerAdvance_layout above. -/
theorem selected_marker_layout
    (outerLeft outerRight : List (Option Bool))
    (witness pref suffix : BitString)
    (b : Bool)
    (hw : witness = pref ++ b :: suffix) :
    witnessPayload pref (b :: suffix) = witness ∧
    (witnessMarkerLayout outerLeft pref (b :: suffix) outerRight).head = none ∧
    (witnessMarkerLayout outerLeft pref (b :: suffix) outerRight).right =
      some b :: (suffix.map some ++ outerRight) := by
  subst witness
  constructor
  · rfl
  constructor
  · rfl
  · simp [witnessMarkerLayout]

#print axioms MCore.Real.P01InputNodePreservingPlan.markerAdvance_layout
#print axioms MCore.Real.P01InputNodePreservingPlan.markerRewind_layout
#print axioms MCore.Real.P01InputNodePreservingPlan.evalStep_input_encoded
#print axioms MCore.Real.P01InputNodePreservingPlan.witness_index_decomposition
#print axioms MCore.Real.P01InputNodePreservingPlan.selected_marker_layout

end P01InputNodePreservingPlan
end Real
end MCore
