import MCore.Real.SourceRecovery
import MCore.Real.P03PerfectFlipDichotomy

namespace MCore
namespace Real
namespace P03UniformRangeDecoder

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02TableauDynamics
open PNPNTMTableauEncoding
open SourceRecovery

/--
A source decoder that receives only the encoded tableau bits.
Unlike decodeSourceBits, it receives neither the source length nor the clock.
This is the exact material interface needed by a physical perfect-flip
candidate.
-/
structure UniformRangeDecoder
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  decode : BitString → Option BitString
  correct :
    ∀ x : BitString,
      decode (R_M M hTotal x) = some x

/--
The existing parameterized source recovery immediately gives the pointwise
existence statement.  What is still missing is one uniform decoder function
that discovers the metadata from the encoded input itself.
-/
theorem pointwise_source_recovery
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ n t,
      decodeSourceBits
          (complementToNTMCandidate M)
          n t
          (R_M M hTotal x) = some x := by
  refine ⟨x.length, M.timeBound x.length, ?_⟩
  simpa [R_M] using decodeSource_reduce M hTotal x

/--
The head block is at a metadata-independent clause position.
This is the first structural fact needed for a uniform decoder.
-/
theorem head_block_offset_independent
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    headBlockOffset (complementToNTMCandidate M) =
      initialStateClauseCount (complementToNTMCandidate M) := by
  rfl

/--
At reduction outputs the decoded circuit is exactly the concrete tableau.
This exposes all clock/radius metadata syntactically inside one circuit.
-/
theorem range_decodes_to_concrete_tableau
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeCircuit (R_M M hTotal x) =
      some
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM
            (complementToNTMCandidate M)
            x
            (M.timeBound x.length))) := by
  simpa [R_M] using decodeCircuit_R_M M hTotal x



/-- A CNF with m clauses produces a circuit AST of size at least m. -/
theorem cnf_clause_count_le_circuit_size
    (F : NTMCNF) :
    F.length ≤ CircuitK1.size (ntmCNFCircuit F) := by
  induction F with
  | nil =>
      simp [ntmCNFCircuit, CircuitK1.size]
  | cons clause rest ih =>
      simp [ntmCNFCircuit, CircuitK1.size]
      omega

/-- The concrete tableau contains enough initial tape material to dominate the
source length at the clause-count level. -/
theorem source_length_le_tableau_clause_count
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    x.length ≤ (boundedExecTableauCNF_NTM M x t).length := by
  unfold boundedExecTableauCNF_NTM
  have hright :
      3 * ntmRadius x t ≤ (ntmInitialCNF M x t).length := by
    unfold ntmInitialCNF
    simp only [List.length_append]
    have hr :=
      length_initial_right_block M x t
    omega
  have hradius : x.length ≤ 3 * ntmRadius x t := by
    unfold ntmRadius
    omega
  omega

/-- On every genuine reduction output, the source length is bounded by the
encoded output length.  This is enough to search source lengths finitely. -/
theorem source_length_le_reduction_length
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    x.length ≤ (R_M M hTotal x).length := by
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  let F := boundedExecTableauCNF_NTM N x t
  have h1 : x.length ≤ F.length := by
    simpa [F, N, t] using
      source_length_le_tableau_clause_count N x t
  have h2 : F.length ≤ CircuitK1.size (ntmCNFCircuit F) :=
    cnf_clause_count_le_circuit_size F
  have h3 :
      CircuitK1.size (ntmCNFCircuit F) ≤
        (encodeCircuit (ntmCNFCircuit F)).length :=
    size_le_encodeCircuit_length (ntmCNFCircuit F)
  have hreduce :
      R_M M hTotal x =
        encodeCircuit (ntmCNFCircuit F) := by
    rfl
  rw [hreduce]
  omega

/-- Clock metadata is arithmetically recoverable from a time-0 head variable
identifier once the candidate is fixed. -/
def recoverClockFromHeadVar
    (M : PolyNTMCandidate)
    (v : Nat) : Nat :=
  v / ntmStateCount M - 1

theorem recoverClockFromHeadVar_correct
    (M : PolyNTMCandidate)
    (t : Nat) :
    recoverClockFromHeadVar M (ntmHeadVar M t 0 none) = t := by
  unfold recoverClockFromHeadVar ntmHeadVar ntmHeadBase ntmStateSlots
  have hpos : 0 < ntmStateCount M := by
    simp [ntmStateCount]
  rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero]
  rw [Nat.mul_div_right _ hpos]
  omega



/--
A source candidate for encoded bits, using only metadata determined by the
candidate and the proposed source length.  The length bound makes the search
space finite on genuine reduction outputs.
-/
structure BoundedSourceCandidate
    (M : PolyDTMCandidate)
    (bits : BitString) where
  source : BitString
  length_le : source.length ≤ bits.length
  decodes :
    decodeSourceBits
        (complementToNTMCandidate M)
        source.length
        (M.timeBound source.length)
        bits = some source

/-- Every real reduction output has at least one bounded source candidate: its
actual source. -/
def genuineSourceCandidate
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    BoundedSourceCandidate M (R_M M hTotal x) :=
  { source := x
    length_le := source_length_le_reduction_length M hTotal x
    decodes := by
      simpa [R_M] using decodeSource_reduce M hTotal x }

/--
Uniqueness of the bounded source candidate would immediately turn the
pointwise decoder into a uniform source decoder on the real reduction range.
This is isolated as a property, not assumed as a theorem.
-/
def BoundedSourceUnique
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ (x : BitString)
    (C : BoundedSourceCandidate M (R_M M hTotal x)),
    C.source = x

theorem boundedSourceUnique_gives_extensional_recovery
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hUnique : BoundedSourceUnique M hTotal)
    (x : BitString)
    (C : BoundedSourceCandidate M (R_M M hTotal x)) :
    C.source = x :=
  hUnique x C

/--
The unresolved metadata question is now an exact uniqueness statement:
the true source is known to be present in a finite length-bounded candidate
space; what remains is to rule out a distinct source satisfying the same
parameterized decoder on the same real reduction output.
-/
def BoundedSourceUniquenessGap : Prop :=
  ∃ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    BoundedSourceUnique M hTotal

/--
The remaining constructive producer for the B branch.
It is deliberately weaker than PerfectFlip: it asks only for uniform recovery
of the previous source from a genuine reduction image.
-/
def UniformRangeDecoderLaw : Prop :=
  ∃ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (UniformRangeDecoder M hTotal)

#print axioms MCore.Real.P03UniformRangeDecoder.pointwise_source_recovery
#print axioms MCore.Real.P03UniformRangeDecoder.head_block_offset_independent
#print axioms MCore.Real.P03UniformRangeDecoder.range_decodes_to_concrete_tableau

end P03UniformRangeDecoder
end Real
end MCore
