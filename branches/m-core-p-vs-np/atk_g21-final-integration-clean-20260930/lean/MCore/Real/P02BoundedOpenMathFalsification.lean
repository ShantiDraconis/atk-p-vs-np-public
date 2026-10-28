import Mathlib.Tactic
import MCore.Real.P02BoundedOpenMath
import MCore.Real.P02BoundedComputationEncoding

namespace MCore
namespace Real
namespace P02BoundedOpenMathFalsification

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02CookLevinFromBoundedExec
open P02BoundedSemanticInput
open P02BoundedFinalBridge
open P02BoundedOpenMath

/-- Real structural criterion for falsifying the current bounded fixed-point
equation.  No imaginary denominator/succCode API is used. -/
def RejectStrictGrowth : Prop :=
  ∀ (M : PolyDTMCandidate) (x : BitString),
    x.length < (encodeCircuit (rejectCircuit M x)).length

theorem strictGrowth_refutes_boundedSameInputEquation
    (hGrow : RejectStrictGrowth) :
    ¬ BoundedSameInputEquation := by
  intro H
  rcases H with H
  let M : PolyDTMCandidate :=
    { stateCount := 0
      machine :=
        { initial := 0
          blank := none
          transition := fun q a => (q, a, .stay)
          halting := fun _ => true }
      blank_none := rfl
      accepting := fun _ => false
      timeBound := fun _ => 0
      time_poly := by
        refine ⟨0, 0, ?_⟩
        intro n
        simp }
  rcases H M with ⟨fuel, code, hEq⟩
  let x := selfInputFuel fuel code
  have hlt := hGrow M x
  have hlen :
      x.length = (encodeCircuit (rejectCircuit M x)).length :=
    congrArg List.length hEq
  omega

theorem strictGrowth_refutes_producer
    (hGrow : RejectStrictGrowth) :
    ¬ UniformBoundedSameInputProducer := by
  intro h
  apply strictGrowth_refutes_boundedSameInputEquation hGrow
  exact boundedSameInputEquation_iff_producer.mpr h

/-- Every circuit encoding is nonempty. -/
theorem encodeCircuit_length_pos
    (c : CircuitK1.Circuit) :
    0 < (encodeCircuit c).length := by
  have hsize : 0 < CircuitK1.size c := by
    cases c <;> simp [CircuitK1.size]
  exact lt_of_lt_of_le hsize (size_le_encodeCircuit_length c)

/-- The CNF circuit encoding contains at least one unit of syntax per clause. -/
theorem cnfCircuit_encode_length_ge_clause_count
    (f : CNF) :
    f.length ≤ (encodeCircuit (cnfCircuit f)).length := by
  induction f with
  | nil =>
      simp [cnfCircuit, encodeCircuit]
  | cons c cs ih =>
      simp [cnfCircuit, encodeCircuit]
      omega

/-- Each initial right-tape cell contributes exactly three symbol clauses. -/
theorem setRightCell_length
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) :
    (setRightCell [] M x t s i target).length = 3 := by
  simp [setRightCell, setSymbolClauses, alphabet]

/-- The initial right-tape block has three clauses per radius cell. -/
theorem initialRightPart_length
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    ((List.range (radius x t)).flatMap fun i =>
      setRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank)).length =
      3 * radius x t := by
  simp [setRightCell, setSymbolClauses, alphabet]
  omega

/-- The concrete tableau has strictly more clauses than input bits. -/
theorem boundedExecTableauCNF_length_gt_input
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    x.length < (boundedExecTableauCNF M x t).length := by
  have hright :
      x.length <
        ((List.range (radius x t)).flatMap fun i =>
          setRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)).length := by
    rw [initialRightPart_length]
    simp [radius]
    omega
  unfold boundedExecTableauCNF initialCNF
  simp only [List.length_append]
  omega

/-- Hence the actual Cook-Levin rejection encoding strictly grows in length. -/
theorem rejectCircuit_strict_growth :
    RejectStrictGrowth := by
  intro M x
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
  unfold rejectCircuit boundedExecCircuit
  exact lt_of_lt_of_le hcnf henc

/-- Falsification of the current bounded OPEN_MATH equation, if all structural
lemmas above kernel-check. -/
theorem not_BoundedSameInputEquation :
    ¬ BoundedSameInputEquation :=
  strictGrowth_refutes_boundedSameInputEquation rejectCircuit_strict_growth

theorem not_UniformBoundedSameInputProducer :
    ¬ UniformBoundedSameInputProducer :=
  strictGrowth_refutes_producer rejectCircuit_strict_growth

#print axioms MCore.Real.P02BoundedOpenMathFalsification.rejectCircuit_strict_growth
#print axioms MCore.Real.P02BoundedOpenMathFalsification.not_BoundedSameInputEquation
#print axioms MCore.Real.P02BoundedOpenMathFalsification.not_UniformBoundedSameInputProducer

end P02BoundedOpenMathFalsification
end Real
end MCore
