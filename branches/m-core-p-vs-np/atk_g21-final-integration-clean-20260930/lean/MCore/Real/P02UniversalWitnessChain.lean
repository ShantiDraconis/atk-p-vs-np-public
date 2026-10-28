import MCore.K10
import MCore.BackwardAudit.OrientedWitnessBoundary
import MCore.Real.P02G21G22Attack
import MCore.Real.P02DiagonalFrontier

namespace MCore
namespace Real
namespace P02WitnessChain

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02TerminalFrontier
open P02DiagonalFrontier
open P02G21G22Attack

/-- Generic historical separation witness retained for K9/K10 interoperability. -/
abbrev GenericSeparationWitness {Language : Type}
    (C : ClassicalComplexityInterface Language) :=
  BackwardAudit.LowerBoundWitness C.inP C.inNP

/-- K10 data tied to one fixed abstract classical interface. -/
structure FixedK10WitnessDataCore {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  α : Type
  Value : Type
  data : SeparationWitnessData Language α Value
  classical_eq : data.interface.classical = C

def k10DataToGenericWitness
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    GenericSeparationWitness W.interface.classical :=
  { language := W.witness
    in_np := W.witness_in_np
    not_in_p := separation_witness_not_in_P W }

def fixedK10ToGenericWitness
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (W : FixedK10WitnessDataCore C) :
    GenericSeparationWitness C := by
  rcases W with ⟨α, Value, data, hclassical⟩
  cases hclassical
  exact k10DataToGenericWitness data

/-- Canonical P02 witness: a failure generator for the fixed canonical SAT language. -/
abbrev UniversalWitness :=
  FailureGenerator SATTarget

/-- Exact existence producer requested by the terminal P02 chain. -/
def UniversalWitnessExists : Prop :=
  Nonempty UniversalWitness

/-- Named OPEN_MATH producer. No inhabitant is asserted here. -/
def UniversalWitnessProducer : Prop :=
  UniversalWitnessExists

/-- The canonical witness-existence object is definitionally the pinned P02 target. -/
theorem universalWitnessExists_iff_p02Target :
    UniversalWitnessExists ↔ P02Target := by
  rfl

/-- Exact requested first edge: witness existence is equivalent to G2.1 pointwise failure. -/
theorem universalWitnessExists_iff_g21Pointwise :
    UniversalWitnessExists ↔ G21Pointwise := by
  rw [universalWitnessExists_iff_p02Target]
  exact g21_pointwise_iff_p02_target.symm

theorem universalWitnessExists_to_g21Pointwise
    (h : UniversalWitnessExists) :
    G21Pointwise :=
  universalWitnessExists_iff_g21Pointwise.mp h

theorem g21Pointwise_to_p02Target
    (h : G21Pointwise) :
    P02Target :=
  g21_pointwise_iff_p02_target.mp h

/-- Visible terminal chain: UniversalWitnessExists -> G21Pointwise -> P02Target. -/
theorem universalWitnessExists_to_p02Target
    (h : UniversalWitnessExists) :
    P02Target :=
  g21Pointwise_to_p02Target
    (universalWitnessExists_to_g21Pointwise h)

/-- Stronger diagonal-family payload already present in the frozen P02 lane. -/
theorem diagonalFamily_to_universalWitnessExists
    (D : DiagonalFamily) :
    UniversalWitnessExists := by
  exact ⟨D.toFailureGenerator⟩

theorem diagonalFixedPointGap_to_universalWitnessExists
    (h : DiagonalFixedPointGap) :
    UniversalWitnessExists := by
  rcases h with ⟨D⟩
  exact diagonalFamily_to_universalWitnessExists D

/-- If P01 is supplied, this exact witness producer closes the internal endpoint. -/
theorem p01_universalWitness_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hU : UniversalWitnessExists) :
    PneqNP :=
  p01_p02_close_internal_separation
    hP01
    (universalWitnessExists_to_p02Target hU)

#print axioms universalWitnessExists_iff_p02Target
#print axioms universalWitnessExists_iff_g21Pointwise
#print axioms universalWitnessExists_to_p02Target
#print axioms diagonalFamily_to_universalWitnessExists
#print axioms diagonalFixedPointGap_to_universalWitnessExists
#print axioms p01_universalWitness_closes_internal

end P02WitnessChain
end Real
end MCore
