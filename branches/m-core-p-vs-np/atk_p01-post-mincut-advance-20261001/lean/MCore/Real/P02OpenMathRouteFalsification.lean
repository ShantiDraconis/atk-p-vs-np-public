import MCore.Real.P02SemanticTransformerCore
import MCore.Real.P02CookLevinSameInputCore
import MCore.Real.P02BoundedComputationEncoding
import MCore.Real.P02SemanticAlignmentCountermodel

namespace MCore
namespace Real
namespace P02OpenMathRouteFalsification

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02TotalCandidateSemanticCore
open P02SemanticTransformerCore
open P02CookLevinSameInputCore

/-- The semantic-alignment route is already refuted by the certified
constant-pair countermodel. -/
theorem not_SemanticAlignmentCore :
    ¬ SemanticAlignmentCore :=
  P02SemanticAlignmentCountermodel.semanticAlignmentCore_refuted

/-- Every circuit encoding is nonempty. -/
theorem encodeCircuit_length_pos
    (c : Circuit) :
    0 < (encodeCircuit c).length := by
  have hsize : 0 < CircuitK1.size c := by
    cases c <;> simp [CircuitK1.size]
  exact Nat.lt_of_lt_of_le hsize (size_le_encodeCircuit_length c)

/-- CNF syntax contributes at least one encoding unit per clause. -/
theorem cnfCircuit_encode_length_ge_clause_count
    (f : CNF) :
    f.length ≤ (encodeCircuit (cnfCircuit f)).length := by
  induction f with
  | nil =>
      simp [cnfCircuit, encodeCircuit]
  | cons c cs ih =>
      simp [cnfCircuit, encodeCircuit]
      omega

theorem setRightCell_length
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) :
    (setRightCell [] M x t s i target).length = 3 := by
  simp [setRightCell, setSymbolClauses, alphabet]

theorem length_le_flatMap_of_one_le
    {α β : Type}
    (xs : List α)
    (f : α → List β)
    (h : ∀ a ∈ xs, 1 ≤ (f a).length) :
    xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil =>
      simp
  | cons a as ih =>
      have ha : 1 ≤ (f a).length := h a (by simp)
      have htail : ∀ b ∈ as, 1 ≤ (f b).length := by
        intro b hb
        exact h b (by simp [hb])
      have hi := ih htail
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

theorem radius_le_initialRightPart_length
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    radius x t ≤
      ((List.range (radius x t)).flatMap fun i =>
        setRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank)).length := by
  have h :=
    length_le_flatMap_of_one_le
      (List.range (radius x t))
      (fun i =>
        setRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank))
      (by
        intro i hi
        rw [setRightCell_length]
        decide)
  simpa using h

theorem boundedExecTableauCNF_length_gt_input
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    x.length < (boundedExecTableauCNF M x t).length := by
  have hradius : x.length < radius x t := by
    simp [radius]
    omega
  have hpart :=
    radius_le_initialRightPart_length M x t
  have hright :
      x.length <
        ((List.range (radius x t)).flatMap fun i =>
          setRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)).length :=
    Nat.lt_of_lt_of_le hradius hpart
  unfold boundedExecTableauCNF initialCNF
  simp only [List.length_append]
  omega

theorem rejectTransform_strict_growth
    (M : PolyDTMCandidate)
    (x : BitString) :
    x.length < (rejectTransform M x).length := by
  let t := M.timeBound x.length
  have hcnf :
      x.length <
        (boundedExecTableauCNF (complementCandidate M) x t).length :=
    boundedExecTableauCNF_length_gt_input (complementCandidate M) x t
  have henc :
      (boundedExecTableauCNF (complementCandidate M) x t).length ≤
        (encodeCircuit
          (cnfCircuit
            (boundedExecTableauCNF (complementCandidate M) x t))).length :=
    cnfCircuit_encode_length_ge_clause_count _
  unfold rejectTransform rejectCircuit boundedExecCircuit
  exact Nat.lt_of_lt_of_le hcnf henc

theorem no_SameInputWitness
    (M : PolyDTMCandidate) :
    ¬ Nonempty (SameInputWitness M) := by
  rintro ⟨W⟩
  have hlt := rejectTransform_strict_growth M W.input
  have hlen :
      W.input.length = (rejectTransform M W.input).length :=
    congrArg List.length W.fixed
  omega

/-- Literal Cook-Levin same-input closure is formally impossible for the
current encoding because the transform strictly grows every input. -/
theorem not_TotalCandidateSameInputCore :
    ¬ TotalCandidateSameInputCore := by
  intro H
  have h := H
    P02SemanticAlignmentCountermodel.constantPairCandidate
    P02SemanticAlignmentCountermodel.constantPair_declared_total
  exact no_SameInputWitness
    P02SemanticAlignmentCountermodel.constantPairCandidate h

#print axioms MCore.Real.P02OpenMathRouteFalsification.not_SemanticAlignmentCore
#print axioms MCore.Real.P02OpenMathRouteFalsification.rejectTransform_strict_growth
#print axioms MCore.Real.P02OpenMathRouteFalsification.not_TotalCandidateSameInputCore

end P02OpenMathRouteFalsification
end Real
end MCore
