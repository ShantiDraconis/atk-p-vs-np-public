import MCore.Real.P02BoundedComputationClose

namespace MCore
namespace Real
namespace P02TableauCompletenessActive

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic
open P02BoundedComputationSoundness
open P02BoundedComputationClose

theorem evalClause_append_true_of_guard_true
    (sigma : Assignment)
    (guard suffix : Clause)
    (hguard : evalClause sigma guard = true) :
    evalClause sigma (guard ++ suffix) = true := by
  rw [evalClause_append, hguard]
  simp

theorem evalCNF_append_true_local
    (sigma : Assignment)
    (a b : CNF)
    (ha : evalCNF sigma a = true)
    (hb : evalCNF sigma b = true) :
    evalCNF sigma (a ++ b) = true := by
  rw [evalCNF_append_eq, ha, hb]
  rfl

theorem inactive_guard_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hinactive : q ≠ config.state ∨ a ≠ config.tape.head) :
    evalClause sigma
      [neg (stateVar M t s q), neg (headVar M t s a)] = true := by
  rcases hmatch with ⟨hstate, hhead, _, _⟩
  rcases hinactive with hq | ha
  · have hs : sigma (stateVar M t s q) = false := by
      have h := hstate q
      simpa [hq] using h
    simp [evalClause, evalLiteral, neg, hs]
  · have hh : sigma (headVar M t s a) = false := by
      have h := hhead a
      simpa [ha] using h
    simp [evalClause, evalLiteral, neg, hh]

theorem setStateClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (setStateClauses guard M t s target) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold setStateClauses at hclause
  rcases List.mem_ofFn.mp hclause with ⟨q, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard _ hguard

theorem setSymbolClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (varAt : Option Bool → Nat)
    (target : Option Bool)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (setSymbolClauses guard varAt target) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold setSymbolClauses at hclause
  rcases List.mem_map.mp hclause with ⟨a, _, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard _ hguard

theorem copySymbolClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copySymbolClauses guard oldVar newVar) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copySymbolClauses at hclause
  rcases List.mem_flatMap.mp hclause with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with hfirst | hrest
  · rw [hfirst]
    exact evalClause_append_true_of_guard_true sigma guard _ hguard
  · rcases hrest with hsecond | hempty
    · rw [hsecond]
      exact evalClause_append_true_of_guard_true sigma guard _ hguard
    · simp at hempty

theorem copyLeftAll_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copyLeftAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyLeftAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i)
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyRightAll_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copyRightAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyRightAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i)
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyLeftCells_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t oldS newS : Nat)
    (indices : List Nat)
    (oldI newI : Nat → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma
      (indices.flatMap fun i =>
        copyLeftCell guard M x t oldS (oldI i) newS (newI i)) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  unfold copyLeftCell at hi
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (leftVar M x t oldS (oldI i))
      (leftVar M x t newS (newI i))
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyRightCells_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t oldS newS : Nat)
    (indices : List Nat)
    (oldI newI : Nat → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma
      (indices.flatMap fun i =>
        copyRightCell guard M x t oldS (oldI i) newS (newI i)) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  unfold copyRightCell at hi
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (rightVar M x t oldS (oldI i))
      (rightVar M x t newS (newI i))
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

def GuardedCNF (guard : Clause) (F : CNF) : Prop :=
  ∀ clause ∈ F, ∃ suffix : Clause, clause = guard ++ suffix

theorem guarded_append
    (guard : Clause) (A B : CNF)
    (hA : GuardedCNF guard A)
    (hB : GuardedCNF guard B) :
    GuardedCNF guard (A ++ B) := by
  intro clause h
  rcases List.mem_append.mp h with h | h
  · exact hA clause h
  · exact hB clause h

theorem setStateClauses_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    GuardedCNF guard (setStateClauses guard M t s target) := by
  intro clause h
  unfold setStateClauses at h
  rcases List.mem_ofFn.mp h with ⟨q, rfl⟩
  exact ⟨[litFor (stateVar M t s q) (decide (q = target))], rfl⟩

theorem setSymbolClauses_guarded
    (guard : Clause)
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    GuardedCNF guard (setSymbolClauses guard varAt target) := by
  intro clause h
  unfold setSymbolClauses at h
  rw [List.mem_map] at h
  rcases h with ⟨a, _, rfl⟩
  exact ⟨[litFor (varAt a) (decide (a = target))], rfl⟩

theorem copySymbolClauses_guarded
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat) :
    GuardedCNF guard (copySymbolClauses guard oldVar newVar) := by
  intro clause h
  unfold copySymbolClauses at h
  rcases List.mem_flatMap.mp h with ⟨a, _, h⟩
  simp only [List.mem_cons, List.mem_singleton] at h
  rcases h with h | h
  · exact ⟨[neg (oldVar a), pos (newVar a)], h⟩
  · rcases h with h | h
    · exact ⟨[pos (oldVar a), neg (newVar a)], h⟩
    · cases h

theorem copyLeftAll_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard (copyLeftAll guard M x t s) := by
  intro clause h
  unfold copyLeftAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact copySymbolClauses_guarded guard
    (leftVar M x t s i) (leftVar M x t (s + 1) i) clause hi

theorem copyRightAll_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard (copyRightAll guard M x t s) := by
  intro clause h
  unfold copyRightAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact copySymbolClauses_guarded guard
    (rightVar M x t s i) (rightVar M x t (s + 1) i) clause hi

theorem setLeftCell_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString)
    (t s i : Nat) (target : Option Bool) :
    GuardedCNF guard (setLeftCell guard M x t s i target) := by
  unfold setLeftCell
  exact setSymbolClauses_guarded guard _ target

theorem setRightCell_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString)
    (t s i : Nat) (target : Option Bool) :
    GuardedCNF guard (setRightCell guard M x t s i target) := by
  unfold setRightCell
  exact setSymbolClauses_guarded guard _ target

theorem copyLeftCell_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) :
    GuardedCNF guard (copyLeftCell guard M x t oldS oldI newS newI) := by
  unfold copyLeftCell
  exact copySymbolClauses_guarded guard _ _

theorem copyRightCell_guarded
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) :
    GuardedCNF guard (copyRightCell guard M x t oldS oldI newS newI) := by
  unfold copyRightCell
  exact copySymbolClauses_guarded guard _ _

theorem flatMap_guarded
    {α : Type}
    (guard : Clause)
    (xs : List α)
    (F : α → CNF)
    (hF : ∀ x ∈ xs, GuardedCNF guard (F x)) :
    GuardedCNF guard (xs.flatMap F) := by
  intro clause h
  rcases List.mem_flatMap.mp h with ⟨x, hx, hc⟩
  exact hF x hx clause hc

theorem haltingCaseCNF_guarded
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    GuardedCNF
      [neg (stateVar M t s q), neg (headVar M t s a)]
      (haltingCaseCNF M x t s q a) := by
  let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
  unfold haltingCaseCNF
  dsimp only
  exact guarded_append guard _ _
    (guarded_append guard _ _
      (guarded_append guard _ _
        (setStateClauses_guarded guard M t (s + 1) q)
        (copySymbolClauses_guarded guard
          (headVar M t s) (headVar M t (s + 1))))
      (copyLeftAll_guarded guard M x t s))
    (copyRightAll_guarded guard M x t s)

theorem stayCaseCNF_guarded
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    GuardedCNF
      [neg (stateVar M t s q), neg (headVar M t s a)]
      (stayCaseCNF M x t s q a qNext write) := by
  let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
  unfold stayCaseCNF
  dsimp only
  exact guarded_append guard _ _
    (guarded_append guard _ _
      (guarded_append guard _ _
        (setStateClauses_guarded guard M t (s + 1) qNext)
        (setSymbolClauses_guarded guard (headVar M t (s + 1)) write))
      (copyLeftAll_guarded guard M x t s))
    (copyRightAll_guarded guard M x t s)

theorem leftMoveCaseCNF_guarded
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    GuardedCNF
      [neg (stateVar M t s q), neg (headVar M t s a)]
      (leftMoveCaseCNF M x t s q a qNext write) := by
  let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
  let r := radius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      copyLeftCell guard M x t s (i + 1) (s + 1) i
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      copyRightCell guard M x t s i (s + 1) (i + 1)
  have hShiftLeft : GuardedCNF guard shiftedLeft := by
    apply flatMap_guarded
    intro i hi
    exact copyLeftCell_guarded guard M x t s (i + 1) (s + 1) i
  have hShiftRight : GuardedCNF guard shiftedRight := by
    apply flatMap_guarded
    intro i hi
    exact copyRightCell_guarded guard M x t s i (s + 1) (i + 1)
  unfold leftMoveCaseCNF
  dsimp only
  exact guarded_append guard _ _
    (guarded_append guard _ _
      (guarded_append guard _ _
        (guarded_append guard _ _
          (guarded_append guard _ _
            (setStateClauses_guarded guard M t (s + 1) qNext)
            (copySymbolClauses_guarded guard
              (leftVar M x t s 0) (headVar M t (s + 1))))
          hShiftLeft)
        (setLeftCell_guarded guard M x t (s + 1) (r - 1) M.machine.blank))
      (setRightCell_guarded guard M x t (s + 1) 0 write))
    hShiftRight

theorem rightMoveCaseCNF_guarded
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    GuardedCNF
      [neg (stateVar M t s q), neg (headVar M t s a)]
      (rightMoveCaseCNF M x t s q a qNext write) := by
  let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
  let r := radius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      copyLeftCell guard M x t s i (s + 1) (i + 1)
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      copyRightCell guard M x t s (i + 1) (s + 1) i
  have hShiftLeft : GuardedCNF guard shiftedLeft := by
    apply flatMap_guarded
    intro i hi
    exact copyLeftCell_guarded guard M x t s i (s + 1) (i + 1)
  have hShiftRight : GuardedCNF guard shiftedRight := by
    apply flatMap_guarded
    intro i hi
    exact copyRightCell_guarded guard M x t s (i + 1) (s + 1) i
  unfold rightMoveCaseCNF
  dsimp only
  exact guarded_append guard _ _
    (guarded_append guard _ _
      (guarded_append guard _ _
        (guarded_append guard _ _
          (guarded_append guard _ _
            (setStateClauses_guarded guard M t (s + 1) qNext)
            (copySymbolClauses_guarded guard
              (rightVar M x t s 0) (headVar M t (s + 1))))
          (setLeftCell_guarded guard M x t (s + 1) 0 write))
        hShiftLeft)
      hShiftRight)
    (setRightCell_guarded guard M x t (s + 1) (r - 1) M.machine.blank)

theorem transitionCaseCNF_guarded
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    GuardedCNF
      [neg (stateVar M t s q), neg (headVar M t s a)]
      (transitionCaseCNF M x t s q a) := by
  by_cases hhalt : M.machine.halting q = true
  · simpa [transitionCaseCNF, hhalt] using
      haltingCaseCNF_guarded M x t s q a
  · rcases htrans : M.machine.transition q a with ⟨qNext, write, dir⟩
    cases dir with
    | stay =>
        simpa [transitionCaseCNF, hhalt, htrans] using
          stayCaseCNF_guarded M x t s q a qNext write
    | left =>
        simpa [transitionCaseCNF, hhalt, htrans] using
          leftMoveCaseCNF_guarded M x t s q a qNext write
    | right =>
        simpa [transitionCaseCNF, hhalt, htrans] using
          rightMoveCaseCNF_guarded M x t s q a qNext write

theorem inactive_transitionCase_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hinactive : q ≠ config.state ∨ a ≠ config.tape.head) :
    evalCNF sigma (transitionCaseCNF M x t s q a) = true := by
  let guard : Clause :=
    [neg (stateVar M t s q), neg (headVar M t s a)]
  have hguard : evalClause sigma guard = true := by
    simpa [guard] using inactive_guard_true sigma M x t s config hmatch q a hinactive
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  have hprefix :
      ∃ suffix : Clause, clause = guard ++ suffix := by
    exact transitionCaseCNF_guarded M x t s q a clause hclause
  rcases hprefix with ⟨suffix, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard suffix hguard

#print axioms MCore.Real.P02TableauCompletenessActive.inactive_guard_true
#print axioms MCore.Real.P02TableauCompletenessActive.inactive_transitionCase_true

end P02TableauCompletenessActive
end Real
end MCore
