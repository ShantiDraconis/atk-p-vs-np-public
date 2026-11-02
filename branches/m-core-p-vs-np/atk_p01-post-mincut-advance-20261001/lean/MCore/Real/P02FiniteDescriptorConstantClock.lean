import MCore.Real.P02FiniteDescriptorLocality
import MCore.Real.P02SemanticTransformerDichotomy

namespace MCore
namespace Real
namespace P02FiniteDescriptorConstantClock

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02FiniteDescriptorReduction
open P02FiniteDescriptorLocality
open P02SemanticTransformerDichotomy

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

theorem getD_append_of_lt_length
    {α : Type}
    (xs ys : List α)
    (i : Nat)
    (d : α)
    (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  induction xs generalizing i with
  | nil =>
      simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [List.getD_cons_zero]
      | succ i =>
          have hi' : i < xs.length := by
            simpa using hi
          simpa [List.getD_cons_succ] using
            ih i hi'

theorem canonical_run_state_eq_of_common_prefix
    {stateCount : Nat}
    (M : TM (Fin (stateCount + 1)) (Option Bool))
    (fuel : Nat)
    (pref tail₁ tail₂ : BitString)
    (hLen : fuel < pref.length) :
    (M.run fuel
        (initialTMConfig M (pref ++ tail₁))).state =
      (M.run fuel
        (initialTMConfig M (pref ++ tail₂))).state := by
  cases pref with
  | nil =>
      simp at hLen
  | cons b bs =>
      apply canonical_run_state_eq_of_right_window M fuel
      · simp [initialTMConfig, inputTape]
      · intro i hi
        have hib : i < bs.length := by
          simp at hLen
          omega
        change
          (((bs ++ tail₁).map some).getD i M.blank) =
            (((bs ++ tail₂).map some).getD i M.blank)
        rw [List.map_append, List.map_append]
        rw [getD_append_of_lt_length
              (bs.map some) (tail₁.map some) i M.blank
              (by simpa using hib)]
        rw [getD_append_of_lt_length
              (bs.map some) (tail₂.map some) i M.blank
              (by simpa using hib)]

def padBlock : BitString :=
  [true, false, false, false, true, false]

def padPrefix : Nat → BitString
  | 0 => []
  | n + 1 => padBlock ++ padPrefix n

def padCNF : Nat → Circuit → Circuit
  | 0, c => c
  | n + 1, c => .and (.const true) (padCNF n c)

theorem encode_padCNF
    (n : Nat)
    (c : Circuit) :
    encodeCircuit (padCNF n c) =
      padPrefix n ++ encodeCircuit c := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [padCNF, padPrefix, padBlock, encodeCircuit, ih,
        List.append_assoc]

theorem padPrefix_length
    (n : Nat) :
    (padPrefix n).length = 6 * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [padPrefix, padBlock, ih]
      omega

theorem padCNF_isCNF
    (n : Nat)
    {c : Circuit}
    (hc : IsCNF c) :
    IsCNF (padCNF n c) := by
  induction n with
  | zero =>
      simpa [padCNF] using hc
  | succ n ih =>
      exact IsCNF_and emptyCNF_isCNF ih

theorem eval_padCNF
    (σ : Assignment)
    (n : Nat)
    (c : Circuit) :
    evalCircuit σ (padCNF n c) = evalCircuit σ c := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [padCNF, evalCircuit, ih]

theorem sat_padCNF_iff
    (n : Nat)
    (c : Circuit)
    (hc : IsCNF c) :
    SATLanguage (padCNF n c) ↔ SATLanguage c := by
  constructor
  · rintro ⟨_, σ, hEval⟩
    refine ⟨hc, σ, ?_⟩
    rw [← eval_padCNF σ n c]
    exact hEval
  · rintro ⟨_, σ, hEval⟩
    refine ⟨padCNF_isCNF n hc, σ, ?_⟩
    rw [eval_padCNF σ n c]
    exact hEval

def paddedFalseBits (n : Nat) : BitString :=
  encodeCircuit (padCNF n (.const false))

def paddedTrueBits (n : Nat) : BitString :=
  encodeCircuit (padCNF n (.const true))

theorem paddedFalse_not_sat
    (n : Nat) :
    ¬ SATTarget (paddedFalseBits n) := by
  intro hSat
  have hPad : SATLanguage (padCNF n (.const false)) :=
    (encoded_sat_equivalence (padCNF n (.const false))).mp hSat
  have hBase : SATLanguage (.const false) :=
    (sat_padCNF_iff n (.const false) emptyClause_isCNF).mp hPad
  simpa [SATLanguage, evalCircuit] using hBase

theorem paddedTrue_sat
    (n : Nat) :
    SATTarget (paddedTrueBits n) := by
  apply (encoded_sat_equivalence (padCNF n (.const true))).mpr
  apply (sat_padCNF_iff n (.const true) emptyCNF_isCNF).mpr
  exact ⟨emptyCNF_isCNF, (fun _ => false), rfl⟩

theorem padded_pair_run_state_eq
    {stateCount : Nat}
    (M : TM (Fin (stateCount + 1)) (Option Bool))
    (fuel : Nat) :
    (M.run fuel
        (initialTMConfig M (paddedFalseBits (fuel + 1)))).state =
      (M.run fuel
        (initialTMConfig M (paddedTrueBits (fuel + 1)))).state := by
  have hPrefix : fuel < (padPrefix (fuel + 1)).length := by
    rw [padPrefix_length]
    omega
  have h :=
    canonical_run_state_eq_of_common_prefix
      M fuel (padPrefix (fuel + 1))
      (encodeCircuit (.const false))
      (encodeCircuit (.const true)) hPrefix
  simpa [paddedFalseBits, paddedTrueBits, encode_padCNF] using h

/-- Every finite descriptor whose monomial clock has exponent zero has an
explicit canonical SAT input on which it fails. No global failure hypothesis
is used. -/
theorem exponent_zero_descriptor_failure
    (D : FiniteDTMDescriptor)
    (hExp : D.exponent = 0) :
    ∃ x : BitString,
      ¬ D.toCandidate.CorrectAt SATTarget x := by
  let n := D.coefficient + 1
  let xFalse := paddedFalseBits n
  let xTrue := paddedTrueBits n
  have hStateRaw :
      (D.machine.run D.coefficient
          (initialTMConfig D.machine xFalse)).state =
        (D.machine.run D.coefficient
          (initialTMConfig D.machine xTrue)).state := by
    simpa [n, xFalse, xTrue] using
      padded_pair_run_state_eq D.machine D.coefficient
  have hState :
      (D.toCandidate.machine.run
          (D.toCandidate.timeBound xFalse.length)
          (initialTMConfig D.toCandidate.machine xFalse)).state =
        (D.toCandidate.machine.run
          (D.toCandidate.timeBound xTrue.length)
          (initialTMConfig D.toCandidate.machine xTrue)).state := by
    simpa [FiniteDTMDescriptor.toCandidate, monomialTimeBound, hExp] using
      hStateRaw
  by_cases hAccFalse :
      D.toCandidate.accepting
          (D.toCandidate.machine.run
            (D.toCandidate.timeBound xFalse.length)
            (initialTMConfig D.toCandidate.machine xFalse)).state = true
  · refine ⟨xFalse, ?_⟩
    intro hCorrect
    have hSat : SATTarget xFalse :=
      hCorrect.2.mp hAccFalse
    exact (paddedFalse_not_sat n) (by simpa [xFalse] using hSat)
  · refine ⟨xTrue, ?_⟩
    intro hCorrect
    have hSatTrue : SATTarget xTrue := by
      simpa [xTrue] using paddedTrue_sat n
    have hAccTrue :
        D.toCandidate.accepting
            (D.toCandidate.machine.run
              (D.toCandidate.timeBound xTrue.length)
              (initialTMConfig D.toCandidate.machine xTrue)).state = true :=
      hCorrect.2.mpr hSatTrue
    apply hAccFalse
    have hAcceptEq :
        D.toCandidate.accepting
            (D.toCandidate.machine.run
              (D.toCandidate.timeBound xFalse.length)
              (initialTMConfig D.toCandidate.machine xFalse)).state =
          D.toCandidate.accepting
            (D.toCandidate.machine.run
              (D.toCandidate.timeBound xTrue.length)
              (initialTMConfig D.toCandidate.machine xTrue)).state :=
      congrArg D.toCandidate.accepting hState
    rw [hAcceptEq]
    exact hAccTrue

#print axioms MCore.Real.P02FiniteDescriptorConstantClock.canonical_run_state_eq_of_common_prefix
#print axioms MCore.Real.P02FiniteDescriptorConstantClock.encode_padCNF
#print axioms MCore.Real.P02FiniteDescriptorConstantClock.sat_padCNF_iff
#print axioms MCore.Real.P02FiniteDescriptorConstantClock.padded_pair_run_state_eq
#print axioms MCore.Real.P02FiniteDescriptorConstantClock.exponent_zero_descriptor_failure

end P02FiniteDescriptorConstantClock
end Real
end MCore
