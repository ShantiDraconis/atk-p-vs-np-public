import MCore.Real.P02DiagonalNoShortcut

namespace MCore
namespace Real
namespace P02CandidateCodeFixedPointCounterprobe

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open P02DeterministicRejectionTableau
open P02SemanticSelfSubstitution
open P02FiniteCandidateDescription
open P02DiagonalNoShortcut

/-- Four-state total machine:
0 moves to the second input bit;
1 branches on that bit;
2 rejects and halts;
3 accepts and halts. -/
def secondBitMachine : TM (Fin 4) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q a =>
      if q = 0 then
        (1, a, .right)
      else if q = 1 then
        match a with
        | some true => (3, a, .stay)
        | _ => (2, a, .stay)
      else
        (q, a, .stay)
    halting := fun q => decide (q = 2 ∨ q = 3) }

def secondBitCandidate : PolyDTMCandidate :=
  { stateCount := 3
    machine := secondBitMachine
    blank_none := rfl
    accepting := fun q => decide (q = 3)
    timeBound := fun _ => 2
    time_poly := by
      refine ⟨2, 0, ?_⟩
      intro n
      simp [PolynomialTimeBound] }

theorem secondBitCandidate_total :
    ∀ x : BitString, OwnClockHalts secondBitCandidate x := by
  intro x
  cases x with
  | nil =>
      simp [OwnClockHalts, secondBitCandidate, secondBitMachine,
        initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
        Tape.write, Tape.move]
  | cons b bs =>
      cases bs with
      | nil =>
          cases b <;>
            simp [OwnClockHalts, secondBitCandidate, secondBitMachine,
              initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
              Tape.write, Tape.move]
      | cons c cs =>
          cases b <;> cases c <;>
            simp [OwnClockHalts, secondBitCandidate, secondBitMachine,
              initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
              Tape.write, Tape.move]

/-- On any input with two cells, the observed output is exactly the second bit. -/
theorem secondBitCandidate_observed
    (b0 b1 : Bool) (tail : BitString) :
    observedBit secondBitCandidate (b0 :: b1 :: tail) = b1 := by
  cases b0 <;> cases b1 <;>
    simp [observedBit, secondBitCandidate, secondBitMachine,
      initialTMConfig, inputTape, TM.run, TM.step, Tape.write, Tape.move]

/-- candidateCode begins with encodeNat stateCount = encodeNat 3,
hence its first two bits are true,true independently of the noncomputable clock tail. -/
theorem candidateCode_second_bit_true :
    ∃ tail : BitString,
      candidateCode secondBitCandidate = true :: true :: tail := by
  unfold candidateCode
  simp [secondBitCandidate, encodeNat]

theorem observed_candidateCode_true :
    observedBit secondBitCandidate (candidateCode secondBitCandidate) = true := by
  rcases candidateCode_second_bit_true with ⟨tail, h⟩
  rw [h]
  exact secondBitCandidate_observed true true tail

/-- Every bounded tableau CNF is nonempty because ntmInitialCNF starts with
one state-setting clause for each member of Fin(stateCount+1), and that type
is nonempty. -/
theorem boundedExecTableauCNF_NTM_ne_nil
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    boundedExecTableauCNF_NTM M x t ≠ [] := by
  unfold boundedExecTableauCNF_NTM ntmInitialCNF
  simp [ntmSetStateClauses]

/-- Therefore every rejectCode starts with the .and circuit tag 100. -/
theorem rejectCode_prefix_100
    (M : PolyDTMCandidate) (x : BitString) :
    ∃ tail : BitString,
      rejectCode M x = true :: false :: false :: tail := by
  unfold rejectCode P02DeterministicRejectionTableau.boundedRejectCircuit_DTM
    boundedExecCircuit_NTM
  have hn :
      boundedExecTableauCNF_NTM
        (P02DeterministicRejectionTableau.complementCandidate M)
        x (M.timeBound x.length) ≠ [] :=
    boundedExecTableauCNF_NTM_ne_nil _ _ _
  cases hcnf :
      boundedExecTableauCNF_NTM
        (P02DeterministicRejectionTableau.complementCandidate M)
        x (M.timeBound x.length) with
  | nil =>
      exact False.elim (hn hcnf)
  | cons c cs =>
      simp [ntmCNFCircuit, encodeCircuit, hcnf]

theorem observed_rejectCode_false
    (x : BitString) :
    observedBit secondBitCandidate (rejectCode secondBitCandidate x) = false := by
  rcases rejectCode_prefix_100 secondBitCandidate x with ⟨tail, h⟩
  rw [h]
  exact secondBitCandidate_observed true false (false :: tail)

/-- Concrete total-clock counterexample to the candidate-code fixed-point route. -/
theorem candidateCodeSemanticFixedPoint_refuted :
    ¬ CandidateCodeSemanticFixedPoint := by
  intro H
  have hfix := H secondBitCandidate secondBitCandidate_total
  rw [observed_candidateCode_true,
      observed_rejectCode_false (candidateCode secondBitCandidate)] at hfix
  contradiction

#print axioms MCore.Real.P02CandidateCodeFixedPointCounterprobe.secondBitCandidate_total
#print axioms MCore.Real.P02CandidateCodeFixedPointCounterprobe.candidateCode_second_bit_true
#print axioms MCore.Real.P02CandidateCodeFixedPointCounterprobe.rejectCode_prefix_100
#print axioms MCore.Real.P02CandidateCodeFixedPointCounterprobe.candidateCodeSemanticFixedPoint_refuted

end P02CandidateCodeFixedPointCounterprobe
end Real
end MCore
