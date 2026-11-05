import MCore.Real.P02SemanticTransformerCore
import MCore.Real.P02CookLevinSameInputCore
import MCore.Real.P02BoundedComputationEncoding

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

/-- Tiny total deterministic candidate which rejects the canonical false
constant and accepts the canonical true constant. -/
def constantPairMachine : TM (Fin 4) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, some false, .right)
        | _ => (2, symbol, .stay)
      else if q = 1 then
        match symbol with
        | some false => (2, some false, .stay)
        | some true => (3, some true, .stay)
        | none => (2, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 2) || (q == 3) }

def constantPairAccepting : Fin 4 → Bool :=
  fun q => q == 3

def constantPairTimeBound : TimeBound :=
  fun _ => 2

theorem constantPairTimeBound_poly :
    PolynomialTimeBound constantPairTimeBound := by
  refine ⟨2, 0, ?_⟩
  intro n
  simp [constantPairTimeBound]

def constantPairCandidate : PolyDTMCandidate :=
  { stateCount := 3
    machine := constantPairMachine
    blank_none := rfl
    accepting := constantPairAccepting
    timeBound := constantPairTimeBound
    time_poly := constantPairTimeBound_poly }

theorem constantPair_declared_total :
    DeclaredClockTotal constantPairCandidate := by
  change ∀ x : BitString,
    constantPairCandidate.machine.HaltsWithin
      (constantPairCandidate.timeBound x.length)
      (initialTMConfig constantPairCandidate.machine x)
  intro x
  simp [constantPairCandidate, constantPairTimeBound,
    constantPairMachine, TM.HaltsWithin, initialTMConfig,
    inputTape, TM.run, TM.step, Tape.write, Tape.move]
  cases x with
  | nil => simp
  | cons b bs =>
      cases b <;>
      simp [TM.run, TM.step, Tape.write, Tape.move,
        constantPairMachine]

theorem constantPair_false_rejects :
    ¬ DeclaredAccept constantPairCandidate (encodeCircuit (.const false)) := by
  simp [DeclaredAccept, constantPairCandidate, constantPairAccepting,
    constantPairTimeBound, constantPairMachine, initialTMConfig,
    inputTape, TM.run, TM.step, Tape.write, Tape.move, encodeCircuit]

theorem constantPair_true_accepts :
    DeclaredAccept constantPairCandidate (encodeCircuit (.const true)) := by
  simp [DeclaredAccept, constantPairCandidate, constantPairAccepting,
    constantPairTimeBound, constantPairMachine, initialTMConfig,
    inputTape, TM.run, TM.step, Tape.write, Tape.move, encodeCircuit]

/-- For this candidate the semantic-negation transformer always flips the
candidate's own declared answer, so no acceptance-alignment point exists. -/
theorem constantPair_no_output_alignment :
    ∀ x : BitString,
      ¬ OutputAcceptanceAligned constantPairCandidate x := by
  intro x
  unfold OutputAcceptanceAligned
  by_cases hx : DeclaredAccept constantPairCandidate x
  · have hbits :
        semanticNegationBits constantPairCandidate x =
          encodeCircuit (.const false) := by
      unfold semanticNegationBits semanticNegationCircuit declaredAcceptBit
      have hb :
          constantPairCandidate.accepting
              (constantPairCandidate.machine.run
                (constantPairCandidate.timeBound x.length)
                (initialTMConfig constantPairCandidate.machine x)).state =
            true := hx
      rw [hb]
      rfl
    rw [hbits]
    intro hiff
    exact constantPair_false_rejects (hiff.mpr hx)
  · have hbit :
        constantPairCandidate.accepting
            (constantPairCandidate.machine.run
              (constantPairCandidate.timeBound x.length)
              (initialTMConfig constantPairCandidate.machine x)).state =
          false := by
      cases h :
          constantPairCandidate.accepting
            (constantPairCandidate.machine.run
              (constantPairCandidate.timeBound x.length)
              (initialTMConfig constantPairCandidate.machine x)).state <;>
        simp_all [DeclaredAccept]
    have hbits :
        semanticNegationBits constantPairCandidate x =
          encodeCircuit (.const true) := by
      unfold semanticNegationBits semanticNegationCircuit declaredAcceptBit
      rw [hbit]
      rfl
    rw [hbits]
    intro hiff
    exact hx (hiff.mp constantPair_true_accepts)

/-- The weakened semantic-alignment route is formally false. -/
theorem not_SemanticAlignmentCore :
    ¬ SemanticAlignmentCore := by
  intro H
  rcases H constantPairCandidate constantPair_declared_total with
    ⟨x, hx⟩
  exact constantPair_no_output_alignment x hx

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

theorem initialRightPart_length
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    ((List.range (radius x t)).flatMap fun i =>
      setRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank)).length =
      3 * radius x t := by
  simp [setRightCell, setSymbolClauses, alphabet]
  omega

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
  have h := H constantPairCandidate constantPair_declared_total
  exact no_SameInputWitness constantPairCandidate h

#print axioms MCore.Real.P02OpenMathRouteFalsification.constantPair_declared_total
#print axioms MCore.Real.P02OpenMathRouteFalsification.constantPair_no_output_alignment
#print axioms MCore.Real.P02OpenMathRouteFalsification.not_SemanticAlignmentCore
#print axioms MCore.Real.P02OpenMathRouteFalsification.rejectTransform_strict_growth
#print axioms MCore.Real.P02OpenMathRouteFalsification.not_TotalCandidateSameInputCore

end P02OpenMathRouteFalsification
end Real
end MCore
