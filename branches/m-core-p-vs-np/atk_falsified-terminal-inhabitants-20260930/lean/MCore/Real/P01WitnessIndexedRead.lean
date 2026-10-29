import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.CanonicalSATNatParserAttack
import MCore.Real.P01FullVerifierStackSemantics

namespace MCore
namespace Real
namespace P01WitnessIndexedRead

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness

/-!
Physical witness-index read boundary for the fixed full verifier.

The canonical input node carries its variable index as unary `encodeNat i`.
The witness is stored to the left of the blank delimiter by
`P01WitnessPreservingPrep.preparedTape`.  A valid implementation must be one
fixed finite-control tape machine; the index remains tape data and is never
stored as an unbounded control-state parameter.
-/

/-- Command layout for an isolated indexed-read macro: witness on the left of
one blank delimiter, unary index at the head. -/
def witnessReadTape (witness : BitString) (i : Nat) : Tape (Option Bool) :=
  match encodeNat i with
  | [] =>
      { left := none :: witness.map some, head := none, right := [] }
  | b :: bs =>
      { left := none :: witness.map some, head := some b, right := bs.map some }

/-- Exact operational payload needed for indexed witness access. -/
structure WitnessIndexedReadCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi)
      (i : Nat) (hi : i < varBound phi),
    machine.HaltsWithin
      (timeBound ((witnessBits w).length + (encodeNat i).length))
      { state := machine.initial,
        tape := witnessReadTape (witnessBits w) i }

  correct : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi)
      (i : Nat) (hi : i < varBound phi),
    accepting
      (machine.run
        (timeBound ((witnessBits w).length + (encodeNat i).length))
        { state := machine.initial,
          tape := witnessReadTape (witnessBits w) i }).state = true ↔
      w ⟨i, hi⟩ = true

/-- Unary index scanning is already available as a fixed three-state
primitive and supplies the source-side counter traversal. -/
theorem unary_index_scan_halts
    (i : Nat) :
    CanonicalSATNatParserAttack.natScanMachine.HaltsWithin (i + 1)
      (CanonicalSATNatParserAttack.natConfig 0 [] (encodeNat i)) := by
  simpa using
    CanonicalSATNatParserAttack.nat_scan_encodeNat_halts_linear i []

/-- Witness length is bounded by the source encoding, so any polynomial
indexed-read macro remains polynomial in the canonical source length. -/
theorem witness_region_linear_bound
    {phi : CircuitK1.Circuit} (w : SATWitness phi) :
    (witnessBits w).length ≤ (encodeCircuit phi).length :=
  witness_bits_linear_bound w

def WitnessIndexedReadGap : Prop :=
  Nonempty WitnessIndexedReadCertificate

#print axioms MCore.Real.P01WitnessIndexedRead.unary_index_scan_halts
#print axioms MCore.Real.P01WitnessIndexedRead.witness_region_linear_bound

end P01WitnessIndexedRead
end Real
end MCore
