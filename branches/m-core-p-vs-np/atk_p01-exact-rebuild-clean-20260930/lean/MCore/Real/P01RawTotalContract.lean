import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01RawMalformedTag
import MCore.Real.P01RawMalformedUnary
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01RawTotalContract

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierInvariant
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject

/-- Canonical assignment induced by the guessed witness. -/
def witnessAssignment (w : BitString) : Assignment :=
  fun i => w.getD i false

/-- Exact structural result of the bounded raw decoder. -/
inductive RawDecodeResult (fuel : Nat) (bits : BitString) : Type
  | malformed
      (h : decodeCircuitCore fuel bits = none)
  | parsed
      (phi : Circuit)
      (tail : BitString)
      (h : decodeCircuitCore fuel bits = some (phi, tail))

def classifyRawDecode (fuel : Nat) (bits : BitString) :
    RawDecodeResult fuel bits := by
  cases h : decodeCircuitCore fuel bits with
  | none => exact .malformed h
  | some p =>
      rcases p with ⟨phi, tail⟩
      exact .parsed phi tail h

/-- A successful raw decode exposes an exact canonical prefix.

This is the bridge needed to reuse the exact positive/negative circuit
producers after a raw structural parse succeeds. -/
theorem decodeCore_success_prefix
    {fuel : Nat} {bits tail : BitString} {phi : Circuit}
    (h : decodeCircuitCore fuel bits = some (phi, tail)) :
    bits = encodeCircuit phi ++ tail := by
  exact P01GuessedWitnessRelation.decodeCircuitCore_sound
    fuel bits phi tail h

/-- Any decoded circuit prefix fits inside the original raw source. -/
theorem decoded_prefix_length_le
    {fuel : Nat} {bits tail : BitString} {phi : Circuit}
    (h : decodeCircuitCore fuel bits = some (phi, tail)) :
    (encodeCircuit phi).length ≤ bits.length := by
  rw [decodeCore_success_prefix h]
  simp

/-- Variables referenced by a successfully decoded prefix fit in any witness
whose length is at least the raw source length. -/
theorem decoded_varBound_le_witness
    {fuel : Nat} {bits tail witness : BitString} {phi : Circuit}
    (h : decodeCircuitCore fuel bits = some (phi, tail))
    (hw : bits.length ≤ witness.length) :
    varBound phi ≤ witness.length := by
  exact Nat.le_trans
    (Nat.le_trans
      (P01GuessedWitnessRelation.varBound_le_encoded_length phi)
      (decoded_prefix_length_le h))
    hw

/-- The witness-induced assignment agrees with physical indexed reads exactly. -/
theorem witnessAssignment_agrees
    (witness : BitString) (phi : Circuit)
    (h : varBound phi ≤ witness.length) :
    ∀ i, i < varBound phi →
      witness.getD i false = witnessAssignment witness i := by
  intro i hi
  rfl

/-- Parsed prefixes are completely handled by the two exact producers:
valid-in-mode prefixes evaluate; invalid-in-mode prefixes physically reject.

No new semantic hypothesis appears here. -/
theorem parsed_prefix_exact_dichotomy
    (witness bits tail : BitString)
    (phi : Circuit)
    (fuel n consumed padding : Nat)
    (frames : List EvalFrame)
    (hdecode : decodeCircuitCore fuel bits = some (phi, tail))
    (hLayout :
      CheckedLayoutBound n consumed bits (encodeEvalFrames frames))
    (hwitness : bits.length ≤ witness.length) :
    (mode : SyntaxMode) →
      (modeCheck mode phi = true →
        ExactBoundedCheckedCircuitRunCertificate
          (witnessAssignment witness) witness mode phi) ∧
      (modeCheck mode phi = false →
        ExactBoundedCheckedCircuitRejectCertificate
          (witnessAssignment witness) witness mode phi) := by
  intro mode
  constructor
  · intro hmode
    exact circuit_exact_bounded_certificate
      (witnessAssignment witness) witness phi mode
  · intro hmode
    exact circuit_exact_bounded_reject
      (witnessAssignment witness) witness phi mode

/-- Physical fail-closed outcome used by malformed raw recursion.

The checked evaluator has two honest failure forms:
* the explicit rejecting state;
* an active dead configuration with no successors.

The latter is intentional: one more run step erases that branch, which the
already-certified verifier determinism lemmas turn into HaltsWithin and
non-acceptance. -/
def EvalFailClosed
    (cfg : Configuration CheckedEvalRunState (Option Bool)) : Prop :=
  cfg.state = .reject ∨
    (¬ Halted checkedEvalRunLoopMachine cfg ∧
      checkedEvalRunLoopMachine.successors cfg = [])

/-- One cubic budget slice pays for a successful canonical prefix evaluation
plus the finite-control handoffs at one raw-decoder recursion level. -/
def rawMalformedSlice (n : Nat) : Nat :=
  8192 * (n + 1) ^ 3

/-- Polynomial raw-rejection budget: one cubic slice per remaining decoder
fuel level.  At the top fuel = source.length + 1, hence this is quartic in the
source length. -/
def rawMalformedBudget (fuel n : Nat) : Nat :=
  (fuel + 1) * rawMalformedSlice n

/-- Raw malformed rejection contract at one fixed decoder fuel. -/
def RawMalformedAtFuel (fuel : Nat) : Prop :=
  ∀ (witness bits : BitString)
      (frames : List EvalFrame)
      (mode : SyntaxMode)
      (consumed padding n : Nat),
    bits.length < fuel →
    decodeCircuitCore fuel bits = none →
    CheckedLayoutBound n consumed bits (encodeEvalFrames frames) →
    bits.length ≤ witness.length →
    ∃ m ≤ rawMalformedBudget fuel n,
      ∃ cfg : Configuration CheckedEvalRunState (Option Bool),
        cfg ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 bits (encodeEvalFrames frames) padding }] ∧
        EvalFailClosed cfg

/-- Terminal raw obligation after all reusable circuit-level machinery has been
factored out: every sufficient-fuel decoder failure must become physical
fail-closed execution. -/
def RawMalformedPhysicalProducer : Prop :=
  ∀ fuel : Nat, RawMalformedAtFuel fuel

/-- Once the raw malformed producer exists, structural raw parsing has no
remaining case outside the exact positive/negative producers. -/
structure RawTotalKernel where
  malformed : RawMalformedPhysicalProducer

#print axioms MCore.Real.P01RawTotalContract.decodeCore_success_prefix
#print axioms MCore.Real.P01RawTotalContract.decoded_prefix_length_le
#print axioms MCore.Real.P01RawTotalContract.decoded_varBound_le_witness
#print axioms MCore.Real.P01RawTotalContract.parsed_prefix_exact_dichotomy

end P01RawTotalContract
end Real
end MCore
