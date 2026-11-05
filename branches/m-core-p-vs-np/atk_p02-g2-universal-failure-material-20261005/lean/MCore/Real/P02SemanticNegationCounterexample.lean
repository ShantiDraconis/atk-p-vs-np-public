import MCore.Real.P02SemanticNegationReduction

namespace MCore
namespace Real
namespace P02SemanticNegationCounterexample

open CanonicalFinalProof
open CanonicalCircuitBits
open P02TotalCandidateFailureMinCut
open P02SemanticInvariantCore
open P02SemanticNegationReduction

/-- Four-state total DTM: move to the second input bit, then accept iff it is true. -/
def secondBitMachine : TM (Fin 4) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        (1, symbol, .right)
      else if q = 1 then
        if symbol = some true then (3, symbol, .stay)
        else (2, symbol, .stay)
      else
        (q, symbol, .stay)
    halting := fun q =>
      if q = 2 then true else if q = 3 then true else false }

def secondBitCandidate : PolyDTMCandidate :=
  { stateCount := 3
    machine := secondBitMachine
    blank_none := rfl
    accepting := fun q => if q = 3 then true else false
    timeBound := fun _ => 2
    time_poly := by
      refine ⟨2, 0, ?_⟩
      intro n
      simp [CanonicalFinalProof.PolynomialTimeBound] }

theorem secondBitCandidate_total :
    DeclaredClockTotal secondBitCandidate := by
  intro x
  cases x with
  | nil =>
      simp [DeclaredClockTotal, secondBitCandidate, secondBitMachine,
        initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
        Tape.write, Tape.move]
  | cons b bs =>
      cases bs with
      | nil =>
          cases b <;>
            simp [DeclaredClockTotal, secondBitCandidate, secondBitMachine,
              initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
              Tape.write, Tape.move]
      | cons b2 rest =>
          cases b <;> cases b2 <;>
            simp [DeclaredClockTotal, secondBitCandidate, secondBitMachine,
              initialTMConfig, inputTape, TM.HaltsWithin, TM.run, TM.step,
              Tape.write, Tape.move]

theorem secondBit_rejects_constFalse :
    ¬ DeclaredAccepts secondBitCandidate
      (encodeCircuit (.const false)) := by
  simp [DeclaredAccepts, secondBitCandidate, secondBitMachine,
    encodeCircuit, initialTMConfig, inputTape, TM.run, TM.step,
    Tape.write, Tape.move]

theorem secondBit_accepts_constTrue :
    DeclaredAccepts secondBitCandidate
      (encodeCircuit (.const true)) := by
  simp [DeclaredAccepts, secondBitCandidate, secondBitMachine,
    encodeCircuit, initialTMConfig, inputTape, TM.run, TM.step,
    Tape.write, Tape.move]

theorem secondBit_semanticNegation_flips
    (x : BitString) :
    ¬ (DeclaredAccepts secondBitCandidate
          (semanticNegationBits secondBitCandidate x) ↔
        DeclaredAccepts secondBitCandidate x) := by
  unfold semanticNegationBits semanticNegationCircuit declaredAcceptBit
  by_cases hx : DeclaredAccepts secondBitCandidate x
  · have hb :
      secondBitCandidate.accepting
        (secondBitCandidate.machine.run
          (secondBitCandidate.timeBound x.length)
          (initialTMConfig secondBitCandidate.machine x)).state = true := hx
    simp [hb, secondBit_rejects_constFalse, hx]
  · have hb :
      secondBitCandidate.accepting
        (secondBitCandidate.machine.run
          (secondBitCandidate.timeBound x.length)
          (initialTMConfig secondBitCandidate.machine x)).state = false := by
      cases hval :
        secondBitCandidate.accepting
          (secondBitCandidate.machine.run
            (secondBitCandidate.timeBound x.length)
            (initialTMConfig secondBitCandidate.machine x)).state
      · rfl
      · exfalso
        exact hx hval
    simp [hb, secondBit_accepts_constTrue, hx]

theorem no_secondBit_semanticNegationInvariant :
    ¬ SemanticNegationInvariantPoint
      secondBitCandidate secondBitCandidate_total := by
  intro h
  rcases h with ⟨W⟩
  exact secondBit_semanticNegation_flips W.source W.invariant

/-- The proposed universal invariant-point frontier for semantic negation is false. -/
theorem semanticNegationInvariant_open_math_refuted :
    ¬ SEMANTIC_NEGATION_INVARIANT_OPEN_MATH := by
  intro H
  exact no_secondBit_semanticNegationInvariant
    (H secondBitCandidate secondBitCandidate_total)

#print axioms MCore.Real.P02SemanticNegationCounterexample.secondBitCandidate_total
#print axioms MCore.Real.P02SemanticNegationCounterexample.secondBit_semanticNegation_flips
#print axioms MCore.Real.P02SemanticNegationCounterexample.no_secondBit_semanticNegationInvariant
#print axioms MCore.Real.P02SemanticNegationCounterexample.semanticNegationInvariant_open_math_refuted

end P02SemanticNegationCounterexample
end Real
end MCore
