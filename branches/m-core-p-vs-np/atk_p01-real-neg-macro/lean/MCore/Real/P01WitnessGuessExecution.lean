import MCore.Real.CanonicalSATWitnessGuessNTM

namespace MCore
namespace Real
namespace P01WitnessGuessExecution

open CanonicalFinalProof
open CanonicalSATWitnessGuessNTM

theorem mem_runBranches_append
    (fuel : Nat)
    (xs ys : List (Configuration (Fin 2) (Option Bool)))
    (z : Configuration (Fin 2) (Option Bool)) :
    z ∈ witnessGuessMachine.runBranches fuel (xs ++ ys) ↔
      z ∈ witnessGuessMachine.runBranches fuel xs ∨
      z ∈ witnessGuessMachine.runBranches fuel ys := by
  induction fuel generalizing xs ys with
  | zero =>
      simp [NTM.runBranches]
  | succ fuel ih =>
      simp only [NTM.runBranches, List.filter_append, List.flatMap_append]
      rw [ih]
      simp only [ih]
      simpa [or_assoc, or_left_comm, or_comm]

theorem runBranches_guess_cons_step
    (fuel : Nat)
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    witnessGuessMachine.runBranches (fuel + 1)
        [guessConfig left (b :: bs)] =
      witnessGuessMachine.runBranches fuel
        [ guessConfig (some false :: left) bs,
          guessConfig (some true :: left) bs ] := by
  rw [NTM.runBranches]
  change witnessGuessMachine.runBranches fuel
      (witnessGuessMachine.successors (guessConfig left (b :: bs))) =
    witnessGuessMachine.runBranches fuel
      [ guessConfig (some false :: left) bs,
        guessConfig (some true :: left) bs ]
  rw [witnessGuess_successors_cons]

theorem witnessGuess_complete_from
    (left : List (Option Bool))
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some ++ left) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig left source] := by
  induction source generalizing left witness with
  | nil =>
      have hwlen : witness.length = 0 := by simpa using hlen
      have hw : witness = [] := List.length_eq_zero_iff.mp hwlen
      subst witness
      simp [NTM.runBranches, witnessGuessMachine, guessConfig, doneConfig,
        NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  | cons b bs ih =>
      cases witness with
      | nil =>
          simp at hlen
      | cons w ws =>
          have hlen' : ws.length = bs.length := by
            simpa using Nat.succ.inj hlen
          have hstep :=
            runBranches_guess_cons_step (bs.length + 1) left b bs
          rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp]
          rw [hstep]
          cases w with
          | false =>
              have hmem := ih (some false :: left) ws hlen'
              have htarget :
                  doneConfig (ws.reverse.map some ++ some false :: left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some false :: left) bs] := by
                simpa [List.append_assoc] using hmem
              have htarget' :
                  doneConfig ((false :: ws).reverse.map some ++ left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some false :: left) bs] := by
                simpa [List.reverse_cons, List.map_append,
                  List.append_assoc] using htarget
              have hmemUnion :=
                (mem_runBranches_append (bs.length + 1)
                  [guessConfig (some false :: left) bs]
                  [guessConfig (some true :: left) bs]
                  (doneConfig ((false :: ws).reverse.map some ++ left))).2
                  (Or.inl htarget')
              simpa using hmemUnion
          | true =>
              have hmem := ih (some true :: left) ws hlen'
              have htarget :
                  doneConfig (ws.reverse.map some ++ some true :: left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some true :: left) bs] := by
                simpa [List.append_assoc] using hmem
              have htarget' :
                  doneConfig ((true :: ws).reverse.map some ++ left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some true :: left) bs] := by
                simpa [List.reverse_cons, List.map_append,
                  List.append_assoc] using htarget
              have hmemUnion :=
                (mem_runBranches_append (bs.length + 1)
                  [guessConfig (some false :: left) bs]
                  [guessConfig (some true :: left) bs]
                  (doneConfig ((true :: ws).reverse.map some ++ left))).2
                  (Or.inr htarget')
              simpa using hmemUnion

theorem witnessGuess_complete
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig [] source] := by
  simpa using witnessGuess_complete_from [] source witness hlen

theorem witnessGuess_halts_from
    (left : List (Option Bool))
    (source : BitString) :
    witnessGuessMachine.HaltsWithin (source.length + 1)
      (guessConfig left source) := by
  unfold NTM.HaltsWithin
  induction source generalizing left with
  | nil =>
      intro reached hmem
      simp [NTM.runBranches, witnessGuessMachine, guessConfig, doneConfig,
        NTM.successors, NTM.stepBranch, Tape.write, Tape.move] at hmem
      subst reached
      exact Or.inl (doneConfig_accepting left)
  | cons b bs ih =>
      intro reached hmem
      have hstep :=
        runBranches_guess_cons_step (bs.length + 1) left b bs
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp] at hmem
      rw [hstep] at hmem
      have hsplit :=
        (mem_runBranches_append (bs.length + 1)
          [guessConfig (some false :: left) bs]
          [guessConfig (some true :: left) bs]
          reached)
      have hmem' :
          reached ∈
              witnessGuessMachine.runBranches (bs.length + 1)
                [guessConfig (some false :: left) bs] ∨
            reached ∈
              witnessGuessMachine.runBranches (bs.length + 1)
                [guessConfig (some true :: left) bs] := by
        exact hsplit.mp (by simpa using hmem)
      rcases hmem' with hfalse | htrue
      · exact ih (some false :: left) reached hfalse
      · exact ih (some true :: left) reached htrue

theorem witnessGuess_halts
    (source : BitString) :
    witnessGuessMachine.HaltsWithin (source.length + 1)
      (guessConfig [] source) :=
  witnessGuess_halts_from [] source

#print axioms MCore.Real.P01WitnessGuessExecution.mem_runBranches_append
#print axioms MCore.Real.P01WitnessGuessExecution.runBranches_guess_cons_step
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete_from
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_halts

end P01WitnessGuessExecution
end Real
end MCore
