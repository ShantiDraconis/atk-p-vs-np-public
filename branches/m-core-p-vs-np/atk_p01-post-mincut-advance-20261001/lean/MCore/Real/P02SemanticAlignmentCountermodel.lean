import MCore.Real.P02SemanticTransformerCore

namespace MCore
namespace Real
namespace P02SemanticAlignmentCountermodel

open CanonicalFinalProof
open CanonicalCircuitBits
open P02TotalCandidateSemanticCore
open P02SemanticTransformerCore

def falseBits : BitString := encodeCircuit (.const false)
def trueBits : BitString := encodeCircuit (.const true)

/-- Tiny total deterministic candidate which rejects the canonical false
Boolean encoding and accepts the canonical true Boolean encoding. -/
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
  intro x
  unfold DeclaredHalts
  cases x with
  | nil =>
      simp [constantPairCandidate, constantPairTimeBound,
        constantPairMachine, initialTMConfig, inputTape,
        TM.HaltsWithin, TM.run, TM.step, Tape.write, Tape.move]
  | cons b bs =>
      cases b with
      | false =>
          cases bs with
          | nil =>
              simp [constantPairCandidate, constantPairTimeBound,
                constantPairMachine, initialTMConfig, inputTape,
                TM.HaltsWithin, TM.run, TM.step, Tape.write, Tape.move]
          | cons b₂ bs₂ =>
              cases b₂ <;>
                simp [constantPairCandidate, constantPairTimeBound,
                  constantPairMachine, initialTMConfig, inputTape,
                  TM.HaltsWithin, TM.run, TM.step, Tape.write, Tape.move]
      | true =>
          simp [constantPairCandidate, constantPairTimeBound,
            constantPairMachine, initialTMConfig, inputTape,
            TM.HaltsWithin, TM.run, TM.step, Tape.write, Tape.move]

theorem constantPair_rejects_falseBits :
    ¬ DeclaredAccept constantPairCandidate falseBits := by
  simp [DeclaredAccept, falseBits, encodeCircuit,
    constantPairCandidate, constantPairTimeBound,
    constantPairMachine, constantPairAccepting,
    initialTMConfig, inputTape, TM.run, TM.step,
    Tape.write, Tape.move]

theorem constantPair_accepts_trueBits :
    DeclaredAccept constantPairCandidate trueBits := by
  simp [DeclaredAccept, trueBits, encodeCircuit,
    constantPairCandidate, constantPairTimeBound,
    constantPairMachine, constantPairAccepting,
    initialTMConfig, inputTape, TM.run, TM.step,
    Tape.write, Tape.move]

theorem semanticNegationBits_eq_false_of_accepts
    (x : BitString)
    (h : DeclaredAccept constantPairCandidate x) :
    semanticNegationBits constantPairCandidate x = falseBits := by
  have hb :
      declaredAcceptBit constantPairCandidate x = true :=
    (declaredAcceptBit_true_iff constantPairCandidate x).mpr h
  simp [semanticNegationBits, semanticNegationCircuit, falseBits, hb]

theorem semanticNegationBits_eq_true_of_rejects
    (x : BitString)
    (h : ¬ DeclaredAccept constantPairCandidate x) :
    semanticNegationBits constantPairCandidate x = trueBits := by
  have hb :
      declaredAcceptBit constantPairCandidate x = false := by
    cases hv : declaredAcceptBit constantPairCandidate x with
    | false => rfl
    | true =>
        exfalso
        exact h ((declaredAcceptBit_true_iff constantPairCandidate x).mp hv)
  simp [semanticNegationBits, semanticNegationCircuit, trueBits, hb]

/-- The weakened output-acceptance alignment route is itself not universal.
For this total candidate the constant negation transformer always sends an
accepted seed to falseBits (rejected), and a rejected seed to trueBits
(accepted). -/
theorem constantPair_no_output_alignment :
    ¬ ∃ x : BitString,
        OutputAcceptanceAligned constantPairCandidate x := by
  rintro ⟨x, hAlign⟩
  by_cases hx : DeclaredAccept constantPairCandidate x
  · have hEq :=
      semanticNegationBits_eq_false_of_accepts x hx
    have hOut :
        ¬ DeclaredAccept constantPairCandidate
          (semanticNegationBits constantPairCandidate x) := by
      simpa [hEq] using constantPair_rejects_falseBits
    exact hOut (hAlign.mpr hx)
  · have hEq :=
      semanticNegationBits_eq_true_of_rejects x hx
    have hOut :
        DeclaredAccept constantPairCandidate
          (semanticNegationBits constantPairCandidate x) := by
      simpa [hEq] using constantPair_accepts_trueBits
    exact hx (hAlign.mp hOut)

theorem semanticAlignmentCore_refuted :
    ¬ SemanticAlignmentCore := by
  intro H
  rcases H constantPairCandidate constantPair_declared_total with ⟨x, hx⟩
  exact constantPair_no_output_alignment ⟨x, hx⟩

#print axioms MCore.Real.P02SemanticAlignmentCountermodel.constantPair_declared_total
#print axioms MCore.Real.P02SemanticAlignmentCountermodel.constantPair_no_output_alignment
#print axioms MCore.Real.P02SemanticAlignmentCountermodel.semanticAlignmentCore_refuted

end P02SemanticAlignmentCountermodel
end Real
end MCore
