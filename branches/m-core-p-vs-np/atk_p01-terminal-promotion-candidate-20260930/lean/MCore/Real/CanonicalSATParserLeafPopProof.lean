import MCore.Real.CanonicalSATParserReturnProof

namespace MCore
namespace Real
namespace CanonicalSATParserLeafPopProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserWorkScanProof

/-- State-13 scan configuration. remaining is ordered from the current head
toward the source/work delimiter. -/
def leafPopScanConfig
    (remaining : List Bool)
    (leftBase right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 13
        tape := { left := leftBase, head := none, right := right } }
  | b :: bs =>
      { state := 13
        tape :=
          { left := bs.map some ++ leftBase
            head := some b
            right := right } }

@[simp] theorem leafPopScanConfig_state
    (remaining : List Bool)
    (leftBase right : List (Option Bool)) :
    (leafPopScanConfig remaining leftBase right).state = (13 : Fin 25) := by
  cases remaining <;> rfl

@[simp] theorem parser_not_halted_13 :
    parserMachine.halting (13 : Fin 25) = false := by decide

/-- Exact parser configuration immediately after state 13 finds the active
slot, writes its false tombstone, and moves one cell left into state 14. -/
def leafAfterPopConfig
    (restTowardLeft : List Bool)
    (leftBase right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 14
    tape :=
      Tape.move none .left
        { left := restTowardLeft.map some ++ leftBase
          head := some false
          right := right } }

theorem leafPop_step_false
    (bs : List Bool)
    (leftBase right : List (Option Bool))
    (hne : bs ≠ []) :
    parserMachine.step
        (leafPopScanConfig (false :: bs) leftBase right) =
      leafPopScanConfig bs leftBase (some false :: right) := by
  cases bs with
  | nil => exact False.elim (hne rfl)
  | cons b tail =>
      simp [leafPopScanConfig, parserMachine, TM.step, Tape.write, Tape.move,
        List.append_assoc]

theorem leafPop_step_true
    (bs : List Bool)
    (leftBase right : List (Option Bool)) :
    parserMachine.step
        (leafPopScanConfig (true :: bs) leftBase right) =
      leafAfterPopConfig bs leftBase right := by
  simp [leafPopScanConfig, leafAfterPopConfig, parserMachine,
    TM.step, Tape.write]

theorem replicate_option_false_rotate
    (k : Nat)
    (right : List (Option Bool)) :
    List.replicate k (some false) ++ some false :: right =
      some false :: (List.replicate k (some false) ++ right) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [List.replicate_succ, ih]

/-- State 13 scans an arbitrary run of false tombstones and consumes the next
active true slot in exactly k+1 steps. -/
theorem leafPop_run_false_prefix
    (k : Nat)
    (restTowardLeft : List Bool)
    (leftBase right : List (Option Bool)) :
    parserMachine.run (k + 1)
        (leafPopScanConfig
          (List.replicate k false ++ true :: restTowardLeft)
          leftBase right) =
      leafAfterPopConfig restTowardLeft leftBase
        (List.replicate k (some false) ++ right) := by
  induction k generalizing right with
  | zero =>
      rw [show 0 + 1 = 1 by rfl]
      rw [show List.replicate 0 false ++ true :: restTowardLeft =
          true :: restTowardLeft by rfl]
      rw [TM.run]
      simp only [leafPopScanConfig_state, parser_not_halted_13,
        Bool.false_eq_true, if_false]
      rw [leafPop_step_true]
      rfl
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [List.replicate_succ, List.cons_append,
        leafPopScanConfig_state, parser_not_halted_13,
        Bool.false_eq_true, if_false]
      rw [leafPop_step_false _ _ _ (by simp)]
      rw [ih (some false :: right)]
      rw [replicate_option_false_rotate k right]

theorem all_false_eq_replicate
    (xs : List Bool)
    (h : ∀ b ∈ xs, b = false) :
    xs = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b = false := h b (by simp)
      have hbs : ∀ x ∈ bs, x = false := by
        intro x hx
        exact h x (by simp [hx])
      subst b
      have hrec := ih hbs
      rw [hrec]
      simp [List.replicate_succ]

/-- Connect the physical state-13 configuration emitted by the leaf work-log
scan to the abstract right-to-left pop scan. -/
theorem afterEndMoveLeft_leaf_eq_popScan
    (pre suffix : List Bool)
    (leftBase : List (Option Bool)) :
    afterEndMoveLeft 13 leftBase (pre ++ true :: suffix) none =
      leafPopScanConfig
        (suffix.reverse ++ true :: pre.reverse)
        leftBase [none] := by
  cases hrev : suffix.reverse with
  | nil =>
      have hs : suffix = [] := by
        simpa using congrArg List.reverse hrev
      subst suffix
      simp [afterEndMoveLeft, leafPopScanConfig, Tape.move,
        List.map_reverse, List.map_append, List.reverse_append,
        List.append_assoc]
  | cons b bs =>
      have hmap :=
        congrArg (List.map (fun x => some x)) hrev
      have hmaprev :
          (suffix.map (fun x => some x)).reverse =
            (b :: bs).map (fun x => some x) := by
        simpa using hmap
      simp [afterEndMoveLeft, leafPopScanConfig, Tape.move,
        List.map_reverse, List.map_append, List.reverse_append,
        List.append_assoc, hrev, hmaprev]

/-- A successful rightmost-active-slot decomposition therefore reaches state
14 after exactly suffix.length+1 pop-search steps. -/
theorem leaf_pop_decomposed
    (pre suffix : List Bool)
    (leftBase : List (Option Bool))
    (hsuffix : ∀ b ∈ suffix, b = false) :
    parserMachine.run (suffix.length + 1)
        (afterEndMoveLeft 13 leftBase
          (pre ++ true :: suffix) none) =
      leafAfterPopConfig pre.reverse leftBase
        (List.replicate suffix.length (some false) ++ [none]) := by
  rw [afterEndMoveLeft_leaf_eq_popScan]
  have hs : suffix = List.replicate suffix.length false :=
    all_false_eq_replicate suffix hsuffix
  have hrs :
      suffix.reverse = List.replicate suffix.length false := by
    rw [hs]
    simp
  rw [hrs]
  exact leafPop_run_false_prefix suffix.length pre.reverse leftBase [none]

-- ATK audit checkpoint: leaf-pop remains a prefix proof; P01 endpoint is not promoted here.
#print axioms MCore.Real.CanonicalSATParserLeafPopProof.leafPop_run_false_prefix
#print axioms MCore.Real.CanonicalSATParserLeafPopProof.afterEndMoveLeft_leaf_eq_popScan
#print axioms MCore.Real.CanonicalSATParserLeafPopProof.leaf_pop_decomposed

end CanonicalSATParserLeafPopProof
end Real
end MCore
