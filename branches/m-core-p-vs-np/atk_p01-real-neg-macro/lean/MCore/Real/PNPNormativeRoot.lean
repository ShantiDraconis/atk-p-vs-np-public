import MCore.Real.PNPHabitant

namespace MCore
namespace Real
namespace PNPNormativeRoot

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open PNPHabitant

/-- Canonical frozen language for the F2 separation attack. -/
abbrev CanonicalTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- The unique normative material-producer gap. -/
def MaterialProducerGap : Prop :=
  CanonicalSATPNPHabitantGap

/-- The mathematical OPEN_MATH core after the NP-membership side is supplied. -/
def OpenMathCore : Prop :=
  UniversalFailure CanonicalTarget

/-- Candidate routes are search strategies for producing OpenMathCore.
They are not additional normative blockers. -/
inductive StrategyRoute where
  | semanticSelfEmbedding
  | kleeneRecursion
  | candidateCodingBridge
  | diagonalFamily
  deriving DecidableEq, Repr

/-- A completed canonical habitant closes the terminal internal claim. -/
theorem material_producer_closes
    (h : MaterialProducerGap) :
    PneqNP := by
  rcases h with ⟨H⟩
  exact canonical_sat_habitant_closes H

/-- Exact decomposition of the unique material producer. -/
theorem material_producer_iff :
    MaterialProducerGap ↔
      InNP CanonicalTarget ∧ OpenMathCore := by
  exact canonical_sat_habitant_gap_iff

#print axioms MCore.Real.PNPNormativeRoot.material_producer_closes
#print axioms MCore.Real.PNPNormativeRoot.material_producer_iff

end PNPNormativeRoot
end Real
end MCore
