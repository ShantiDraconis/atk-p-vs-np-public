import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATWitness
import MCore.Real.CanonicalSATVerifier
import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.P01FullVerifierPhysicalStackV2

namespace MCore
namespace Real
namespace P01PhysicalVerifierFoundations

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01FullVerifierStackSemantics
open P01FullVerifierPhysicalStackV2

/-- Canonical circuit encoding is injective because the certified decoder is a
left inverse.  No separate coding axiom is needed. -/
theorem encodeCircuit_injective :
    ∀ ⦃a b : CircuitK1.Circuit⦄, encodeCircuit a = encodeCircuit b → a = b := by
  intro a b h
  have hdec := congrArg decodeCircuit h
  have hsome : some a = some b := by
    simpa only [decodeCircuit_encode] using hdec
  exact Option.some.inj hsome

/-- The verifier witness never exceeds the canonical encoded-input length.
This is the exact bound needed by the physical witness shuttle. -/
theorem witness_fits_canonical_input
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi) :
    (witnessBits w).length ≤ (encodeCircuit phi).length :=
  witness_bits_linear_bound w

/-- The semantic stack program is also linearly bounded by canonical encoded
input length. -/
theorem program_fits_canonical_input
    (phi : CircuitK1.Circuit) :
    (evalProgram phi).length ≤ (encodeCircuit phi).length :=
  evalProgram_length_le_encoding phi

/-- Concrete three-symbol interpretation of the physical alphabet.
0 = blank, 1 = false, 2 = true. -/
def alphabetCode : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def alphabetDecode : Fin 3 → Option Bool
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => some false
  | ⟨2, _⟩ => some true

@[simp] theorem alphabetDecode_code
    (s : Option Bool) :
    alphabetDecode (alphabetCode s) = s := by
  cases s with
  | none => rfl
  | some b =>
      cases b <;> rfl

theorem alphabetCode_injective :
    ∀ ⦃a b : Option Bool⦄, alphabetCode a = alphabetCode b → a = b := by
  intro a b h
  have := congrArg alphabetDecode h
  simpa using this

/-- Acceptance interpretation for the final Boolean stack cell.
Blank and false reject; true accepts. -/
def physicalResultAccept : Option Bool → Bool
  | some true => true
  | _ => false

@[simp] theorem physicalResultAccept_blank :
    physicalResultAccept none = false := rfl

@[simp] theorem physicalResultAccept_false :
    physicalResultAccept (some false) = false := rfl

@[simp] theorem physicalResultAccept_true :
    physicalResultAccept (some true) = true := rfl

theorem physicalResultAccept_iff
    (b : Bool) :
    physicalResultAccept (some b) = true ↔ b = true := by
  cases b <;> decide

/-- The V2 representation keeps source and witness as immutable structural
suffixes of the left tape while the mutable stack grows in front of them. -/
theorem stackV2_preserves_source_witness_suffix
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat) :
    (physicalStackV2Tape witness source stack padding).left =
      stack.map some ++ none :: source.reverse.map some ++ none :: witness.map some := by
  rfl

/-- The high-level evaluator produces exactly one Boolean result from an empty
stack, for every circuit and assignment. -/
theorem evaluator_finishes_singleton
    (sigma : Assignment)
    (phi : CircuitK1.Circuit) :
    runProgram sigma (evalProgram phi) [] =
      some [evalCircuit sigma phi] :=
  evalProgram_correct sigma phi

/-- The proof architecture measures runtime in encoded input length itself.
Consequently no unjustified AST-size-to-encoding upper bound is required:
all already-certified bounds are stated directly in |encodeCircuit phi|. -/
def canonicalInputSize (phi : CircuitK1.Circuit) : Nat :=
  (encodeCircuit phi).length

@[simp] theorem canonicalInputSize_eq
    (phi : CircuitK1.Circuit) :
    canonicalInputSize phi = (encodeCircuit phi).length := rfl

#print axioms MCore.Real.P01PhysicalVerifierFoundations.encodeCircuit_injective
#print axioms MCore.Real.P01PhysicalVerifierFoundations.witness_fits_canonical_input
#print axioms MCore.Real.P01PhysicalVerifierFoundations.program_fits_canonical_input
#print axioms MCore.Real.P01PhysicalVerifierFoundations.alphabetCode_injective
#print axioms MCore.Real.P01PhysicalVerifierFoundations.evaluator_finishes_singleton

end P01PhysicalVerifierFoundations
end Real
end MCore
