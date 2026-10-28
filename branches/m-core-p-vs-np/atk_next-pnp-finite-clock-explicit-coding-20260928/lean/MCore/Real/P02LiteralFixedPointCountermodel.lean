import MCore.Real.P02LiteralFixedPointFirewall

namespace MCore
namespace Real
namespace P02LiteralFixedPointCountermodel

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02LiteralFixedPointFirewall
open P02ClockedDiagonalCompiler

/-- A tiny deterministic machine that is correct on the two constant canonical
SAT encodings.  It reads only the first two tag bits:
  00 -> reject (.const false)
  01 -> accept (.const true)
No claim is made about any other input. -/
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

theorem constantPair_false_correct :
    constantPairCandidate.CorrectAt
      (SATBits circuitBitEncoding) falseBits := by
  unfold PolyDTMCandidate.CorrectAt
  constructor
  ·
    simp [TM.HaltsWithin, constantPairCandidate, constantPairTimeBound,
      constantPairMachine, initialTMConfig, inputTape, TM.run, TM.step,
      Tape.write, Tape.move, falseBits, encodeCircuit]
  · constructor
    · intro h
      have : False := by
        simpa [constantPairCandidate, constantPairAccepting,
          constantPairTimeBound, constantPairMachine,
          initialTMConfig, inputTape, TM.run, TM.step,
          Tape.write, Tape.move, falseBits, encodeCircuit] using h
      contradiction
    · intro hsat
      exact False.elim (falseBits_not_sat hsat)

theorem constantPair_true_correct :
    constantPairCandidate.CorrectAt
      (SATBits circuitBitEncoding) trueBits := by
  unfold PolyDTMCandidate.CorrectAt
  constructor
  ·
    simp [TM.HaltsWithin, constantPairCandidate, constantPairTimeBound,
      constantPairMachine, initialTMConfig, inputTape, TM.run, TM.step,
      Tape.write, Tape.move, trueBits, encodeCircuit]
  · constructor
    · intro _
      exact trueBits_sat
    · intro _
      decide

/-- The literal fixed-point strategy is not merely unproved: the current
two-constant semantic transformer cannot supply a fixed point for every
polynomial deterministic candidate. -/
theorem no_universal_literal_fixed_point :
    ¬ ∀ M : PolyDTMCandidate,
        ∃ x : BitString, semanticDiagonalBits M x = x := by
  intro h
  have hfix := h constantPairCandidate
  exact
    (no_literal_fixed_point_if_constants_correct
      constantPairCandidate
      constantPair_false_correct
      constantPair_true_correct) hfix

#print axioms MCore.Real.P02LiteralFixedPointCountermodel.constantPairTimeBound_poly
#print axioms MCore.Real.P02LiteralFixedPointCountermodel.constantPair_false_correct
#print axioms MCore.Real.P02LiteralFixedPointCountermodel.constantPair_true_correct
#print axioms MCore.Real.P02LiteralFixedPointCountermodel.no_universal_literal_fixed_point

end P02LiteralFixedPointCountermodel
end Real
end MCore
