import MCore.Real.P02CanonicalNormalization
import MCore.Real.P02TerminalFrontier
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02DiagonalFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open P02TerminalFrontier

/-- Acceptance bit observed at the candidate's own declared polynomial clock. -/
def AcceptsAtDeclaredBound
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- Syntactic validity in the existing canonical Circuit encoding. -/
def CanonicalSATValid (x : BitString) : Prop :=
  ∃ phi : CircuitK1.Circuit, decodeCircuit x = some phi

/-- One genuine diagonal witness against one deterministic candidate.

The crucial field is semantic, not a literal string equation:
SAT(x_M) iff M does not accept x_M at its declared bound.
No claim is made here that such a witness exists. -/
structure DiagonalCounterexampleWitness (M : PolyDTMCandidate) where
  bits : BitString
  valid : CanonicalSATValid bits
  flips :
    SATBits circuitBitEncoding bits ↔
      ¬ AcceptsAtDeclaredBound M bits

/-- Once a semantic diagonal witness exists, it is automatically an input on
which the candidate is not CorrectAt for canonical SAT. -/
theorem diagonal_witness_fails
    (M : PolyDTMCandidate)
    (W : DiagonalCounterexampleWitness M) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) W.bits := by
  intro hcorrect
  unfold PolyDTMCandidate.CorrectAt at hcorrect
  rcases hcorrect with ⟨_, hdecides⟩
  by_cases hacc : AcceptsAtDeclaredBound M W.bits
  · have hsat : SATBits circuitBitEncoding W.bits :=
      hdecides.mp hacc
    exact (W.flips.mp hsat) hacc
  · have hsat : SATBits circuitBitEncoding W.bits :=
      W.flips.mpr hacc
    exact hacc (hdecides.mpr hsat)

/-- Effective-family-shaped G2.1 payload.  This is stronger than the bare
existential UniversalFailure because it supplies the counterexample as data for
every candidate.  It still does not assert computability of this function in
the recursion-theoretic sense; that would require a separate machine coding. -/
structure DiagonalFamily where
  witness : ∀ M : PolyDTMCandidate, DiagonalCounterexampleWitness M

def DiagonalFixedPointGap : Prop :=
  Nonempty DiagonalFamily

def DiagonalFamily.toFailureGenerator
    (D : DiagonalFamily) :
    FailureGenerator (SATBits circuitBitEncoding) :=
  { counterexample := fun M => (D.witness M).bits
    fails := fun M => diagonal_witness_fails M (D.witness M) }

theorem diagonal_family_closes_p02
    (D : DiagonalFamily) :
    P02Target := by
  exact ⟨D.toFailureGenerator⟩

theorem diagonal_fixed_point_gap_closes_p02
    (h : DiagonalFixedPointGap) :
    P02Target := by
  rcases h with ⟨D⟩
  exact diagonal_family_closes_p02 D

/-
A polynomial bound in |description(M)| is intentionally not asserted here:
the current repository has no certified canonical encoding/size function for
PolyDTMCandidate descriptions.  Such a bound belongs to a stronger effective
enumeration/diagonalization route and must not be fabricated as part of G2.
-/

#print axioms MCore.Real.P02DiagonalFrontier.diagonal_witness_fails
#print axioms MCore.Real.P02DiagonalFrontier.diagonal_family_closes_p02
#print axioms MCore.Real.P02DiagonalFrontier.diagonal_fixed_point_gap_closes_p02

end P02DiagonalFrontier
end Real
end MCore
