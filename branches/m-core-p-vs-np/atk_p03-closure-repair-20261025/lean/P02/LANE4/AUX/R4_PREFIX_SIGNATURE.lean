import P02.LANE4.AUX.R4_TRANSITION_LENGTH
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace R4_PREFIX_SIGNATURE

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- Initial state clauses are singleton clauses because their guard is empty. -/
theorem ntmSetStateClauses_nil_clause_length_one
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (c : NTMClause)
    (hc : c ∈ ntmSetStateClauses [] M t s target) :
    c.length = 1 := by
  simp [ntmSetStateClauses] at hc
  rcases hc with ⟨q, rfl⟩
  simp

/-- Initial symbol clauses are singleton clauses because their guard is empty. -/
theorem ntmSetSymbolClauses_nil_clause_length_one
    (varAt : Option Bool → Nat)
    (target : Option Bool)
    (c : NTMClause)
    (hc : c ∈ ntmSetSymbolClauses [] varAt target) :
    c.length = 1 := by
  simp [ntmSetSymbolClauses, ntmAlphabet] at hc
  rcases hc with rfl | rfl | rfl
  all_goals simp

theorem ntmSetLeftCell_nil_clause_length_one
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s i : Nat)
    (target : Option Bool)
    (c : NTMClause)
    (hc : c ∈ ntmSetLeftCell [] M x t s i target) :
    c.length = 1 := by
  exact ntmSetSymbolClauses_nil_clause_length_one
    (ntmLeftVar M x t s i) target c
    (by simpa [ntmSetLeftCell] using hc)

theorem ntmSetRightCell_nil_clause_length_one
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s i : Nat)
    (target : Option Bool)
    (c : NTMClause)
    (hc : c ∈ ntmSetRightCell [] M x t s i target) :
    c.length = 1 := by
  exact ntmSetSymbolClauses_nil_clause_length_one
    (ntmRightVar M x t s i) target c
    (by simpa [ntmSetRightCell] using hc)

/-- Every clause in the initial tableau block has exactly one literal. -/
theorem ntmInitialCNF_clause_length_one
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (c : NTMClause)
    (hc : c ∈ ntmInitialCNF M x t) :
    c.length = 1 := by
  simp only [ntmInitialCNF, List.mem_append, List.mem_flatMap,
    List.mem_range] at hc
  rcases hc with hState | hRest
  · exact ntmSetStateClauses_nil_clause_length_one M t 0 M.machine.initial c hState
  · rcases hRest with hHead | hRest
    · exact ntmSetSymbolClauses_nil_clause_length_one
        (ntmHeadVar M t 0) (inputTape x).head c hHead
    · rcases hRest with hLeft | hRight
      · rcases hLeft with ⟨i, hi, hic⟩
        exact ntmSetLeftCell_nil_clause_length_one
          M x t 0 i ((inputTape x).left.getD i M.machine.blank) c hic
      · rcases hRight with ⟨i, hi, hic⟩
        exact ntmSetRightCell_nil_clause_length_one
          M x t 0 i ((inputTape x).right.getD i M.machine.blank) c hic

/-- The explicit active-choice guard begins with two literals, hence is never
an initial singleton clause. -/
theorem ntmGuardChoiceClause_length_ge_two
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    2 ≤ (ntmGuardChoiceClause M x t s q a).length := by
  simp [ntmGuardChoiceClause]

/-- Every clause emitted by a choice guard has exactly two literals. -/
theorem ntmChoiceGuardCNF_clause_length_two
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (j : Nat)
    (c : NTMClause)
    (hc : c ∈ ntmChoiceGuardCNF M x t s q a j) :
    c.length = 2 := by
  simp [ntmChoiceGuardCNF] at hc
  rcases hc with rfl | rfl
  all_goals simp

/-- Every at-most-one choice clause, when present, has exactly two literals. -/
theorem ntmAtMostOneChoiceCNF_clause_length_two
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (c : NTMClause)
    (hc : c ∈ ntmAtMostOneChoiceCNF M x t s q a) :
    c.length = 2 := by
  unfold ntmAtMostOneChoiceCNF at hc
  simp only [List.mem_flatMap] at hc
  rcases hc with ⟨j, hj, hc⟩
  rcases hc with ⟨k, hk, hc⟩
  split at hc
  · simp at hc
    rcases hc with rfl
    simp
  · simp at hc

#print axioms P02.LANE4.AUX.R4_PREFIX_SIGNATURE.ntmInitialCNF_clause_length_one
#print axioms P02.LANE4.AUX.R4_PREFIX_SIGNATURE.ntmGuardChoiceClause_length_ge_two
#print axioms P02.LANE4.AUX.R4_PREFIX_SIGNATURE.ntmChoiceGuardCNF_clause_length_two
#print axioms P02.LANE4.AUX.R4_PREFIX_SIGNATURE.ntmAtMostOneChoiceCNF_clause_length_two

end R4_PREFIX_SIGNATURE
end AUX
end LANE4
end P02
