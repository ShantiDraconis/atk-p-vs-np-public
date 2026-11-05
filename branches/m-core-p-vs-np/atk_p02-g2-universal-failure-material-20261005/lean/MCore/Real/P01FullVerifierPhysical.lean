import MCore.Real.P01FullVerifierTraversal
import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.P01FullVerifierMachine

namespace MCore
namespace Real
namespace P01FullVerifierPhysical

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01WitnessPreservingPrep
open P01FullVerifierTraversal
open P01FullVerifierStackSemantics

/-- The real verifier tape alphabet has only Bool cells plus blank.  The blank
cell is therefore the unique separator between witness, source and value-stack
regions. -/
def witnessRegion (t : Tape (Option Bool)) : List (Option Bool) :=
  t.left.drop 1

/-- Read the i-th witness cell from the prepared tape's left region. -/
def readWitnessIndexed
    (t : Tape (Option Bool)) (i : Nat) : Option Bool :=
  (witnessRegion t).getD i none

theorem preparedTape_witness_region
    (w : BitString) (b : Bool) (bs : BitString) :
    witnessRegion (preparedTape w (b :: bs)) = w.map some := by
  rfl

theorem readWitnessIndexed_correct
    (w : BitString) (b : Bool) (bs : BitString)
    (i : Nat) (hi : i < w.length) :
    readWitnessIndexed (preparedTape w (b :: bs)) i =
      some w[i] := by
  simp [readWitnessIndexed, witnessRegion, preparedTape, hi]

/-- At the source-end blank, the entire immutable witness/source prefix is on
the left of the head.  This is the physical base point for value-stack work. -/
theorem source_end_preserves_witness_and_source
    (w source : BitString) :
    sourceEndScanner.run (source.length + 1)
      (scanConfig (none :: w.map some) source) =
      { state := (1 : Fin 2),
        tape :=
          { left := source.reverse.map some ++ none :: w.map some,
            head := none,
            right := [] } } := by
  simpa using sourceEndScanner_run (none :: w.map some) source

/-- Canonical representation of a Boolean value stack with its top under the
head.  The immutable verifier prefix remains in the left field. -/
def valueStackTape
    (basePrefix : List (Option Bool)) : List Bool → Tape (Option Bool)
  | [] =>
      { left := basePrefix, head := none, right := [] }
  | v :: vs =>
      { left := basePrefix, head := some v, right := vs.map some }

def stackPushCert
    (basePrefix : List (Option Bool)) (v : Bool) (stack : List Bool) :
    Tape (Option Bool) :=
  valueStackTape basePrefix (v :: stack)

def stackPopCert
    (basePrefix : List (Option Bool)) :
    List Bool → Option (Bool × Tape (Option Bool))
  | [] => none
  | v :: vs => some (v, valueStackTape basePrefix vs)

theorem stackPush_preserves_prefix
    (basePrefix : List (Option Bool)) (v : Bool) (stack : List Bool) :
    (stackPushCert basePrefix v stack).left = basePrefix := by
  rfl

theorem stackPop_preserves_prefix
    (basePrefix : List (Option Bool)) (v : Bool) (stack : List Bool) :
    match stackPopCert basePrefix (v :: stack) with
    | none => False
    | some (_, t) => t.left = basePrefix := by
  cases stack <;> rfl

theorem stackPop_push_inverse
    (basePrefix : List (Option Bool)) (v : Bool) (stack : List Bool) :
    stackPopCert basePrefix (v :: stack) =
      some (v, valueStackTape basePrefix stack) := by
  rfl


/-- Exact representation of the mutable Boolean stack on the physical tape.
The immutable source/witness prefix is carried explicitly as basePrefix. -/
def PhysicalStackRep
    (tape : Tape (Option Bool))
    (basePrefix : List (Option Bool))
    (stack : List Bool) : Prop :=
  tape = valueStackTape basePrefix stack

theorem physicalStackRep_empty
    (basePrefix : List (Option Bool)) :
    PhysicalStackRep (valueStackTape basePrefix []) basePrefix [] := by
  rfl

theorem physicalStackRep_push
    {tape : Tape (Option Bool)}
    {basePrefix : List (Option Bool)}
    {stack : List Bool}
    (v : Bool)
    (hrep : PhysicalStackRep tape basePrefix stack) :
    PhysicalStackRep
      (stackPushCert basePrefix v stack)
      basePrefix (v :: stack) := by
  rfl

theorem physicalStackRep_pop
    (basePrefix : List (Option Bool))
    (stack : List Bool) :
    PhysicalStackRep
      (valueStackTape basePrefix stack)
      basePrefix stack := by
  rfl

theorem physicalStackRep_preserves_prefix
    {tape : Tape (Option Bool)}
    {basePrefix : List (Option Bool)}
    {stack : List Bool}
    (hrep : PhysicalStackRep tape basePrefix stack) :
    tape.left = basePrefix := by
  rw [hrep]
  cases stack <;> rfl

/-- Exact remaining realization object.  It is intentionally not inhabited
here: an inhabitant must be one fixed finite-control TM and must simulate the
certified logical stack semantics on the real verifier tape. -/
structure PhysicalVerifierRealization where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
      machine.HaltsWithin
        (timeBound (encodeCircuit phi).length)
        { state := machine.initial,
          tape := P01FullVerifierMachine.verifierInputTape
            (witnessBits w) (encodeCircuit phi) }
  physical_eq_logical :
    ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
      accepting
        (machine.run
          (timeBound (encodeCircuit phi).length)
          { state := machine.initial,
            tape := P01FullVerifierMachine.verifierInputTape
              (witnessBits w) (encodeCircuit phi) }).state = true ↔
        verifyWitness phi w = true

def PhysicalVerifierGap : Prop :=
  Nonempty PhysicalVerifierRealization

def PhysicalVerifierRealization.toFullVerifierCertificate
    (R : PhysicalVerifierRealization) :
    P01FullVerifierMachine.FullVerifierCertificate where
  stateCount := R.stateCount
  machine := R.machine
  blank_none := R.blank_none
  accepting := R.accepting
  timeBound := R.timeBound
  time_poly := R.time_poly
  halts := R.halts
  correct := R.physical_eq_logical

theorem physical_realization_closes_full_verifier
    (R : PhysicalVerifierRealization) :
    P01FullVerifierMachine.FullVerifierGap :=
  ⟨R.toFullVerifierCertificate⟩

#print axioms MCore.Real.P01FullVerifierPhysical.readWitnessIndexed_correct
#print axioms MCore.Real.P01FullVerifierPhysical.source_end_preserves_witness_and_source
#print axioms MCore.Real.P01FullVerifierPhysical.stackPop_push_inverse
#print axioms MCore.Real.P01FullVerifierPhysical.physicalStackRep_push
#print axioms MCore.Real.P01FullVerifierPhysical.physicalStackRep_preserves_prefix
#print axioms MCore.Real.P01FullVerifierPhysical.physical_realization_closes_full_verifier

end P01FullVerifierPhysical
end Real
end MCore
