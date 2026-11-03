import MCore.Real.P02TableauCompletenessActive
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02TableauCompletenessClose

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic
open P02BoundedComputationSoundness
open P02BoundedComputationClose
open P02TableauCompletenessActive

theorem copySymbolClauses_satisfied_of_assignment_eq
    (sigma : Assignment)
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat)
    (hvals : ∀ a : Option Bool, sigma (oldVar a) = sigma (newVar a)) :
    evalCNF sigma (copySymbolClauses guard oldVar newVar) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copySymbolClauses at hclause
  rcases List.mem_flatMap.mp hclause with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with hfirst | hrest
  · subst clause
    rw [evalClause_append]
    have hv := hvals a
    cases hold : sigma (oldVar a) <;>
      cases hnew : sigma (newVar a) <;>
      simp_all [evalClause, evalLiteral, neg, pos]
  · rcases hrest with hsecond | himpossible
    · subst clause
      rw [evalClause_append]
      have hv := hvals a
      cases hold : sigma (oldVar a) <;>
        cases hnew : sigma (newVar a) <;>
        simp_all [evalClause, evalLiteral, neg, pos]
    · simp at himpossible

theorem copyLeftAll_satisfied
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hvals :
      ∀ i : Nat, i < radius x t →
        ∀ a : Option Bool,
          sigma (leftVar M x t s i a) =
            sigma (leftVar M x t (s + 1) i a)) :
    evalCNF sigma (copyLeftAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyLeftAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
  have hcell :=
    copySymbolClauses_satisfied_of_assignment_eq
      sigma guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i)
      (hvals i (by simpa using hi))
  exact evalCNF_member_true sigma
    (copySymbolClauses guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i))
    clause hc hcell

theorem copyRightAll_satisfied
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hvals :
      ∀ i : Nat, i < radius x t →
        ∀ a : Option Bool,
          sigma (rightVar M x t s i a) =
            sigma (rightVar M x t (s + 1) i a)) :
    evalCNF sigma (copyRightAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyRightAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
  have hcell :=
    copySymbolClauses_satisfied_of_assignment_eq
      sigma guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i)
      (hvals i (by simpa using hi))
  exact evalCNF_member_true sigma
    (copySymbolClauses guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i))
    clause hc hcell

theorem evalCNF_append_true
    (sigma : Assignment)
    (a b : CNF)
    (ha : evalCNF sigma a = true)
    (hb : evalCNF sigma b = true) :
    evalCNF sigma (a ++ b) = true := by
  rw [evalCNF_append_eq, ha, hb]
  rfl

theorem active_halting_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext : SnapshotMatches sigma M x t (s + 1) config) :
    evalCNF sigma
      (haltingCaseCNF M x t s config.state config.tape.head) = true := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) config.state) = true := by
    exact setStateClauses_satisfied_of_assignment
      sigma guard M t (s + 1) config.state hstate1
  have hh :
      evalCNF sigma (copyHeadCell guard M t s (s + 1)) = true := by
    unfold copyHeadCell
    apply copySymbolClauses_satisfied_of_assignment_eq
    intro a
    rw [hhead0 a, hhead1 a]
  have hl :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply copyLeftAll_satisfied
    intro i hi a
    rw [hleft0 i hi a, hleft1 i hi a]
  have hr :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply copyRightAll_satisfied
    intro i hi a
    rw [hright0 i hi a, hright1 i hi a]
  unfold haltingCaseCNF
  simpa [guard, List.append_assoc] using
    evalCNF_append_true sigma
      (setStateClauses guard M t (s + 1) config.state)
      (copyHeadCell guard M t s (s + 1) ++
        copyLeftAll guard M x t s ++
        copyRightAll guard M x t s)
      hs
      (evalCNF_append_true sigma
        (copyHeadCell guard M t s (s + 1))
        (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        hh
        (evalCNF_append_true sigma
          (copyLeftAll guard M x t s)
          (copyRightAll guard M x t s) hl hr))

theorem active_stay_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .stay))
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext :
      SnapshotMatches sigma M x t (s + 1) (M.machine.step config)) :
    evalCNF sigma
      (stayCaseCNF M x t s config.state config.tape.head qNext write) = true := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hstepState : (M.machine.step config).state = qNext := by
    simp [TM.step, htrans]
  have hstepHead : (M.machine.step config).tape.head = write := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hstepLeft :
      (M.machine.step config).tape.left = config.tape.left := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hstepRight :
      (M.machine.step config).tape.right = config.tape.right := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply setStateClauses_satisfied_of_assignment
    intro q
    rw [hstate1 q, hstepState]
  have hh :
      evalCNF sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write) = true := by
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hhead1 a, hstepHead]
  have hl :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply copyLeftAll_satisfied
    intro i hi a
    rw [hleft0 i hi a, hleft1 i hi a, hstepLeft]
  have hr :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply copyRightAll_satisfied
    intro i hi a
    rw [hright0 i hi a, hright1 i hi a, hstepRight]
  unfold stayCaseCNF
  simpa [guard, List.append_assoc] using
    evalCNF_append_true sigma
      (setStateClauses guard M t (s + 1) qNext)
      (setSymbolClauses guard (headVar M t (s + 1)) write ++
        copyLeftAll guard M x t s ++
        copyRightAll guard M x t s)
      hs
      (evalCNF_append_true sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write)
        (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        hh
        (evalCNF_append_true sigma
          (copyLeftAll guard M x t s)
          (copyRightAll guard M x t s) hl hr))

theorem active_left_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hslt : s < t)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .left))
    (hleftBoundary :
      config.tape.left.getD (radius x t) M.machine.blank =
        M.machine.blank)
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext :
      SnapshotMatches sigma M x t (s + 1) (M.machine.step config)) :
    evalCNF sigma
      (leftMoveCaseCNF M x t s config.state config.tape.head qNext write) = true := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hstepState : (M.machine.step config).state = qNext := by
    simp [TM.step, htrans]
  have hstepHead :
      (M.machine.step config).tape.head =
        config.tape.left.getD 0 M.machine.blank := by
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_left_head_getD
        M.machine.blank (config.tape.write write)
  have hstepLeft :
      ∀ i : Nat,
        (M.machine.step config).tape.left.getD i M.machine.blank =
          config.tape.left.getD (i + 1) M.machine.blank := by
    intro i
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_left_left_getD
        M.machine.blank (config.tape.write write) i
  have hstepRightZero :
      (M.machine.step config).tape.right.getD 0 M.machine.blank = write := by
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_left_right_zero
        M.machine.blank (config.tape.write write)
  have hstepRightSucc :
      ∀ i : Nat,
        (M.machine.step config).tape.right.getD (i + 1) M.machine.blank =
          config.tape.right.getD i M.machine.blank := by
    intro i
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_left_right_succ
        M.machine.blank (config.tape.write write) i
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply setStateClauses_satisfied_of_assignment
    intro q
    rw [hstate1 q, hstepState]
  have hh :
      evalCNF sigma
        (copySymbolClauses guard
          (leftVar M x t s 0)
          (headVar M t (s + 1))) = true := by
    apply copySymbolClauses_satisfied_of_assignment_eq
    intro a
    rw [hleft0 0 (by simp [radius]) a, hhead1 a, hstepHead]
  have hshiftLeft :
      evalCNF sigma
        ((List.range (radius x t - 1)).flatMap fun i =>
          copyLeftCell guard M x t s (i + 1) (s + 1) i) = true := by
    apply evalCNF_true_of_forall_mem
    intro clause hclause
    rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
    have his : i < radius x t - 1 := by simpa using hi
    have hiOld : i + 1 < radius x t := by
      have hbase : i < x.length + t := by
        simpa [radius] using his
      simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
    have hiNew : i < radius x t := by
      exact Nat.lt_trans his (Nat.sub_lt (radius_pos x t) (by decide))
    have hcell :
        evalCNF sigma
          (copyLeftCell guard M x t s (i + 1) (s + 1) i) = true := by
      unfold copyLeftCell
      apply copySymbolClauses_satisfied_of_assignment_eq
      intro a
      rw [hleft0 (i + 1) hiOld a, hleft1 i hiNew a, hstepLeft i]
    exact evalCNF_member_true sigma
      (copyLeftCell guard M x t s (i + 1) (s + 1) i)
      clause hc hcell
  have hlast : radius x t - 1 < radius x t := by
    exact Nat.sub_lt (radius_pos x t) (by decide)
  have hidx : radius x t - 1 + 1 = radius x t := by
    exact Nat.sub_add_cancel (radius_pos x t)
  have hstepLeftLast :
      (M.machine.step config).tape.left.getD
          (radius x t - 1) M.machine.blank =
        M.machine.blank := by
    rw [hstepLeft (radius x t - 1), hidx, hleftBoundary]
  have hsetLeft :
      evalCNF sigma
        (setLeftCell guard M x t (s + 1) (radius x t - 1)
          M.machine.blank) = true := by
    unfold setLeftCell
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hleft1 (radius x t - 1) hlast a, hstepLeftLast]
  have hsetRight :
      evalCNF sigma
        (setRightCell guard M x t (s + 1) 0 write) = true := by
    unfold setRightCell
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hright1 0 (by simp [radius]) a, hstepRightZero]
  have hshiftRight :
      evalCNF sigma
        ((List.range (radius x t - 1)).flatMap fun i =>
          copyRightCell guard M x t s i (s + 1) (i + 1)) = true := by
    apply evalCNF_true_of_forall_mem
    intro clause hclause
    rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
    have his : i < radius x t - 1 := by simpa using hi
    have hiOld : i < radius x t := by
      exact Nat.lt_trans his (Nat.sub_lt (radius_pos x t) (by decide))
    have hiNew : i + 1 < radius x t := by
      have hbase : i < x.length + t := by
        simpa [radius] using his
      simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
    have hcell :
        evalCNF sigma
          (copyRightCell guard M x t s i (s + 1) (i + 1)) = true := by
      unfold copyRightCell
      apply copySymbolClauses_satisfied_of_assignment_eq
      intro a
      rw [hright0 i hiOld a, hright1 (i + 1) hiNew a, hstepRightSucc i]
    exact evalCNF_member_true sigma
      (copyRightCell guard M x t s i (s + 1) (i + 1))
      clause hc hcell
  unfold leftMoveCaseCNF
  dsimp [guard] at hs hh hshiftLeft hsetLeft hsetRight hshiftRight ⊢
  simp only [evalCNF_append_eq, List.append_assoc]
  simp [hs, hh, hshiftLeft, hsetLeft, hsetRight, hshiftRight]

theorem active_right_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hslt : s < t)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .right))
    (hrightBoundary :
      config.tape.right.getD (radius x t) M.machine.blank =
        M.machine.blank)
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext :
      SnapshotMatches sigma M x t (s + 1) (M.machine.step config)) :
    evalCNF sigma
      (rightMoveCaseCNF M x t s config.state config.tape.head qNext write) = true := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hstepState : (M.machine.step config).state = qNext := by
    simp [TM.step, htrans]
  have hstepHead :
      (M.machine.step config).tape.head =
        config.tape.right.getD 0 M.machine.blank := by
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_right_head_getD
        M.machine.blank (config.tape.write write)
  have hstepRight :
      ∀ i : Nat,
        (M.machine.step config).tape.right.getD i M.machine.blank =
          config.tape.right.getD (i + 1) M.machine.blank := by
    intro i
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_right_right_getD
        M.machine.blank (config.tape.write write) i
  have hstepLeftZero :
      (M.machine.step config).tape.left.getD 0 M.machine.blank = write := by
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_right_left_zero
        M.machine.blank (config.tape.write write)
  have hstepLeftSucc :
      ∀ i : Nat,
        (M.machine.step config).tape.left.getD (i + 1) M.machine.blank =
          config.tape.left.getD i M.machine.blank := by
    intro i
    simpa [TM.step, htrans, Tape.write] using
      P02BoundedComputationTape.move_right_left_succ
        M.machine.blank (config.tape.write write) i
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply setStateClauses_satisfied_of_assignment
    intro q
    rw [hstate1 q, hstepState]
  have hh :
      evalCNF sigma
        (copySymbolClauses guard
          (rightVar M x t s 0)
          (headVar M t (s + 1))) = true := by
    apply copySymbolClauses_satisfied_of_assignment_eq
    intro a
    rw [hright0 0 (by simp [radius]) a, hhead1 a, hstepHead]
  have hsetLeft :
      evalCNF sigma
        (setLeftCell guard M x t (s + 1) 0 write) = true := by
    unfold setLeftCell
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hleft1 0 (by simp [radius]) a, hstepLeftZero]
  have hshiftLeft :
      evalCNF sigma
        ((List.range (radius x t - 1)).flatMap fun i =>
          copyLeftCell guard M x t s i (s + 1) (i + 1)) = true := by
    apply evalCNF_true_of_forall_mem
    intro clause hclause
    rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
    have his : i < radius x t - 1 := by simpa using hi
    have hiOld : i < radius x t := by
      exact Nat.lt_trans his (Nat.sub_lt (radius_pos x t) (by decide))
    have hiNew : i + 1 < radius x t := by
      have hbase : i < x.length + t := by
        simpa [radius] using his
      simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
    have hcell :
        evalCNF sigma
          (copyLeftCell guard M x t s i (s + 1) (i + 1)) = true := by
      unfold copyLeftCell
      apply copySymbolClauses_satisfied_of_assignment_eq
      intro a
      rw [hleft0 i hiOld a, hleft1 (i + 1) hiNew a, hstepLeftSucc i]
    exact evalCNF_member_true sigma
      (copyLeftCell guard M x t s i (s + 1) (i + 1))
      clause hc hcell
  have hshiftRight :
      evalCNF sigma
        ((List.range (radius x t - 1)).flatMap fun i =>
          copyRightCell guard M x t s (i + 1) (s + 1) i) = true := by
    apply evalCNF_true_of_forall_mem
    intro clause hclause
    rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
    have his : i < radius x t - 1 := by simpa using hi
    have hiOld : i + 1 < radius x t := by
      have hbase : i < x.length + t := by
        simpa [radius] using his
      simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
    have hiNew : i < radius x t := by
      exact Nat.lt_trans his (Nat.sub_lt (radius_pos x t) (by decide))
    have hcell :
        evalCNF sigma
          (copyRightCell guard M x t s (i + 1) (s + 1) i) = true := by
      unfold copyRightCell
      apply copySymbolClauses_satisfied_of_assignment_eq
      intro a
      rw [hright0 (i + 1) hiOld a, hright1 i hiNew a, hstepRight i]
    exact evalCNF_member_true sigma
      (copyRightCell guard M x t s (i + 1) (s + 1) i)
      clause hc hcell
  have hlast : radius x t - 1 < radius x t := by
    exact Nat.sub_lt (radius_pos x t) (by decide)
  have hidx : radius x t - 1 + 1 = radius x t := by
    exact Nat.sub_add_cancel (radius_pos x t)
  have hstepRightLast :
      (M.machine.step config).tape.right.getD
          (radius x t - 1) M.machine.blank =
        M.machine.blank := by
    rw [hstepRight (radius x t - 1), hidx, hrightBoundary]
  have hsetRight :
      evalCNF sigma
        (setRightCell guard M x t (s + 1) (radius x t - 1)
          M.machine.blank) = true := by
    unfold setRightCell
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hright1 (radius x t - 1) hlast a, hstepRightLast]
  unfold rightMoveCaseCNF
  dsimp [guard] at hs hh hsetLeft hshiftLeft hshiftRight hsetRight ⊢
  simp only [evalCNF_append_eq, List.append_assoc]
  simp [hs, hh, hsetLeft, hshiftLeft, hshiftRight, hsetRight]

theorem active_transitionCase_true
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t) :
    evalCNF (executionAssignment M x t)
      (transitionCaseCNF M x t s
        (M.machine.run s (initialTMConfig M.machine x)).state
        (M.machine.run s (initialTMConfig M.machine x)).tape.head) = true := by
  let sigma := executionAssignment M x t
  let init := initialTMConfig M.machine x
  let config := M.machine.run s init
  have hnow :
      SnapshotMatches sigma M x t s config := by
    simpa [sigma, config, init] using
      executionAssignment_snapshot_matches M x t s (Nat.le_of_lt hs)
  have hrunSucc :
      M.machine.run (s + 1) init = M.machine.run 1 config := by
    simpa [config] using
      (MachineRunLemmas.run_add M.machine s 1 init)
  by_cases hhalt : M.machine.halting config.state = true
  · have hnextEq :
        M.machine.run (s + 1) init = config := by
      rw [hrunSucc]
      simpa [TM.run, hhalt]
    have hnext :
        SnapshotMatches sigma M x t (s + 1) config := by
      have h :=
        executionAssignment_snapshot_matches M x t (s + 1)
          (Nat.succ_le_of_lt hs)
      simpa [sigma, init, hnextEq] using h
    simpa [transitionCaseCNF, hhalt, sigma, config, init] using
      active_halting_case_true sigma M x t s config hnow hnext
  · have hhaltFalse : M.machine.halting config.state = false := by
      cases hh : M.machine.halting config.state <;> simp_all
    rcases htrans : M.machine.transition config.state config.tape.head with
      ⟨qNext, write, dir⟩
    have hnextEq :
        M.machine.run (s + 1) init = M.machine.step config := by
      rw [hrunSucc]
      simp [TM.run, hhaltFalse]
    have hnext :
        SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
      have h :=
        executionAssignment_snapshot_matches M x t (s + 1)
          (Nat.succ_le_of_lt hs)
      simpa [sigma, init, hnextEq] using h
    cases dir with
    | stay =>
        simpa [transitionCaseCNF, hhaltFalse, htrans, sigma, config, init] using
          active_stay_case_true sigma M x t s config
            qNext write htrans hnow hnext
    | left =>
        have hboundary :
            config.tape.left.getD (radius x t) M.machine.blank =
              M.machine.blank := by
          simpa [config, init] using
            P02BoundedComputationTape.canonical_run_left_radius_blank
              M x t s (Nat.le_of_lt hs)
        simpa [transitionCaseCNF, hhaltFalse, htrans, sigma, config, init] using
          active_left_case_true sigma M x t s config
            qNext write hs htrans hboundary hnow hnext
    | right =>
        have hboundary :
            config.tape.right.getD (radius x t) M.machine.blank =
              M.machine.blank := by
          simpa [config, init] using
            P02BoundedComputationTape.canonical_run_right_radius_blank
              M x t s (Nat.le_of_lt hs)
        simpa [transitionCaseCNF, hhaltFalse, htrans, sigma, config, init] using
          active_right_case_true sigma M x t s config
            qNext write hs htrans hboundary hnow hnext

theorem transitionCase_true_of_executionAssignment
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    evalCNF (executionAssignment M x t)
      (transitionCaseCNF M x t s q a) = true := by
  let sigma := executionAssignment M x t
  let config := M.machine.run s (initialTMConfig M.machine x)
  have hmatch :
      SnapshotMatches sigma M x t s config := by
    simpa [sigma, config] using
      executionAssignment_snapshot_matches M x t s (Nat.le_of_lt hs)
  by_cases hq : q = config.state
  · by_cases ha : a = config.tape.head
    · subst q
      subst a
      simpa [sigma, config] using active_transitionCase_true M x t s hs
    · exact inactive_transitionCase_true sigma M x t s config
        hmatch q a (Or.inr ha)
  · exact inactive_transitionCase_true sigma M x t s config
      hmatch q a (Or.inl hq)

theorem executionAssignment_transitionStepCNF
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t) :
    evalCNF (executionAssignment M x t)
      (transitionStepCNF M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold transitionStepCNF at hclause
  rcases List.mem_flatten.mp hclause with ⟨block, hblock, hc⟩
  rcases List.mem_ofFn.mp hblock with ⟨q, rfl⟩
  rcases List.mem_flatMap.mp hc with ⟨a, _, hcase⟩
  have htrue :=
    transitionCase_true_of_executionAssignment M x t s hs q a
  exact evalCNF_member_true
    (executionAssignment M x t)
    (transitionCaseCNF M x t s q a)
    clause hcase htrue

theorem executionAssignment_transitionsCNF
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    evalCNF (executionAssignment M x t)
      (transitionsCNF M x t) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold transitionsCNF at hclause
  rcases List.mem_flatMap.mp hclause with ⟨s, hs, hc⟩
  have hslt : s < t := by simpa using hs
  have hstep :=
    executionAssignment_transitionStepCNF M x t s hslt
  exact evalCNF_member_true
    (executionAssignment M x t)
    (transitionStepCNF M x t s)
    clause hc hstep

theorem executionAssignment_boundedExecTableauCNF
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (hacc : AcceptsAtFuel M x t) :
    evalCNF (executionAssignment M x t)
      (boundedExecTableauCNF M x t) = true := by
  unfold boundedExecTableauCNF
  rw [evalCNF_append_eq, evalCNF_append_eq]
  have hi := executionAssignment_initialCNF M x t
  have ht := executionAssignment_transitionsCNF M x t
  have hf := executionAssignment_finalAcceptanceCNF M x t hacc
  simp [hi, ht, hf]

noncomputable def tableauCompletenessCertificate :
    TableauCompletenessCertificate where
  assignment := fun M x t _ => executionAssignment M x t
  satisfies := by
    intro M x t hacc
    exact executionAssignment_boundedExecTableauCNF M x t hacc

theorem tableauCompletenessGap_closed :
    TableauCompletenessGap :=
  ⟨tableauCompletenessCertificate⟩

theorem boundedExecCorrectness_closed :
    BoundedExecCorrectness :=
  certificates_close_boundedExecCorrectness
    transitionSoundnessCertificate
    tableauCompletenessCertificate

#print axioms MCore.Real.P02TableauCompletenessClose.copySymbolClauses_satisfied_of_assignment_eq
#print axioms MCore.Real.P02TableauCompletenessClose.active_halting_case_true
#print axioms MCore.Real.P02TableauCompletenessClose.active_stay_case_true
#print axioms MCore.Real.P02TableauCompletenessClose.active_left_case_true
#print axioms MCore.Real.P02TableauCompletenessClose.active_right_case_true
#print axioms MCore.Real.P02TableauCompletenessClose.executionAssignment_transitionsCNF
#print axioms MCore.Real.P02TableauCompletenessClose.tableauCompletenessCertificate
#print axioms MCore.Real.P02TableauCompletenessClose.boundedExecCorrectness_closed

end P02TableauCompletenessClose
end Real
end MCore
