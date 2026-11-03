import MCore.Real.PNPCookLevinMaterialMinCut
import MCore.Real.PNPNTMTableauFrontier
import MCore.Real.PNPNTMPathFrontier
import MCore.Real.PNPNTMTableauEncoding
import MCore.Real.PNPNTMTableauClosure
import MCore.Real.P02TableauSourceRecovery
import MCore.Real.P02ComplementRunRealization
import MCore.Real.P02BehavioralAlignment

import P02.LANE4.AUX.R1_R3_REAL
import P02.LANE4.AUX.R2_R4_RADIUS
import P02.LANE4.AUX.R4_R5_BOUNDED
import P02.LANE4.AUX.R4_TRANSITION_LENGTH
import P02.LANE4.AUX.R4_PREFIX_SIGNATURE
import P02.LANE4.AUX.R4_PREFIX_MAXIMAL
import P02.LANE4.AUX.R4_TRANSITION_HEAD
import P02.LANE4.AUX.R4_TRANSITION_HEAD_FINAL
import P02.LANE4.AUX.R4_INITIAL_INJECTIVE
import P02.LANE4.AUX.R4_INITIAL_CNF_DECODER
import P02.LANE4.AUX.R4_FINAL
import P02.LANE4.AUX.R4_FIXED_FUEL
import P02.LANE4.AUX.R5_PAIR_INJECTIVE
import P02.LANE4.AUX.R5_PAIR
import P02.LANE4.StructuralClosure
import P02.LANE4.AUX.STRUCTURAL_CLOSURE

import P02.LANE4.OPEN_MATH.BehavioralAlignment
import P02.LANE4.OPEN_MATH.FuelCounterexample
import P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound

namespace P02
namespace LANE4
namespace StructureBundle

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding
open MCore.Real.P02BehavioralAlignment

/-- Structural layer 0: the Cook--Levin/NTM tableau source chain is present. -/
structure BaseStructure where
  tableau_frontier :
    MCore.Real.PNPNTMTableauFrontier.NTMTableauProducer → Prop
  path_type :
    ∀ M : PolyNTMCandidate,
      Type

def baseStructure : BaseStructure where
  tableau_frontier := fun _ => True
  path_type := fun M =>
    Fin (M.timeBound 0 + 1) →
      MCore.Real.PNPNTMPathFrontier.NTMConfig M

/-- Structural layer 1: source/tape and CNF/circuit information preservation. -/
structure R1R3Structure where
  input_injective : Function.Injective inputTape
  cnf_circuit_injective :
    Function.Injective ntmCNFCircuit

def r1r3Structure : R1R3Structure where
  input_injective :=
    AUX.R1_R3_REAL.inputTape_injective
  cnf_circuit_injective :=
    AUX.R1_R3_REAL.ntmCNFCircuit_injective

/-- Structural layer 2: initial dimensions/radius are recoverable. -/
structure R2Structure where
  initial_dimension :
    ∀ (M : PolyNTMCandidate)
      {x y : BitString}
      {t : Nat},
      ntmInitialCNF M x t = ntmInitialCNF M y t →
      x.length = y.length

def r2Structure : R2Structure where
  initial_dimension :=
    AUX.R2_R4_RADIUS.initial_dim_extract_real

/-- Structural layer 4: fixed-fuel bounded encoding is injective. -/
structure R4Structure where
  tableau_fixed_fuel :
    ∀ (M : PolyNTMCandidate) (t : Nat),
      Function.Injective (fun x =>
        boundedExecTableauCNF_NTM M x t)
  circuit_fixed_fuel :
    ∀ (M : PolyNTMCandidate) (t : Nat),
      Function.Injective (fun x =>
        boundedExecCircuit_NTM M x t)

def r4Structure : R4Structure where
  tableau_fixed_fuel :=
    AUX.R4_FINAL.boundedExecTableau_same_params_injective
  circuit_fixed_fuel :=
    AUX.R4_FINAL.boundedExecCircuit_same_params_injective

/-- Structural layer 5: the pair (source,fuel) and the complement reduction
are injective without assuming an injective timeBound. -/
structure R5Structure where
  tableau_pair :
    ∀ (M : PolyNTMCandidate)
      {x y : BitString}
      {tx ty : Nat},
      boundedExecTableauCNF_NTM M x tx =
        boundedExecTableauCNF_NTM M y ty →
      tx = ty ∧ x = y
  circuit_pair :
    ∀ (M : PolyNTMCandidate)
      {x y : BitString}
      {tx ty : Nat},
      boundedExecCircuit_NTM M x tx =
        boundedExecCircuit_NTM M y ty →
      tx = ty ∧ x = y
  complement_reduce :
    ∀ (M : PolyDTMCandidate)
      (hTotal :
        MCore.Real.P02TotalCandidateKleeneReduction.DeclaredClockTotal M),
      Function.Injective
        (MCore.Real.P02ComplementRunRealization.complementSemanticReduction
          M hTotal).reduce

def r5Structure : R5Structure where
  tableau_pair :=
    AUX.R5_PAIR_INJECTIVE.boundedExecTableau_pair_injective
  circuit_pair :=
    AUX.R5_PAIR_INJECTIVE.boundedExecCircuit_pair_injective
  complement_reduce :=
    AUX.R5_PAIR_INJECTIVE.reduce_M_injective_final

/-- Complete AUX structural package.  T10 is intentionally not a field. -/
structure AUXStructure where
  r1r3 : R1R3Structure
  r2 : R2Structure
  r4 : R4Structure
  r5 : R5Structure
  aggregate : P02.LANE4.StructuralClosure

def auxStructure : AUXStructure where
  r1r3 := r1r3Structure
  r2 := r2Structure
  r4 := r4Structure
  r5 := r5Structure
  aggregate := P02.LANE4.structuralClosure

/-- The only semantic endpoint still outside AUX. -/
abbrev T10OpenMath : Prop :=
  MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer

/-- AUX structure plus a genuine T10 producer reaches the exact-diagonal
producer.  This theorem is compositional only. -/
theorem aux_plus_t10_to_exact
    (_A : AUXStructure)
    (T : T10OpenMath) :
    MCore.Real.P02ExactDiagonalFrontier.TotalExactDiagonalProducer :=
  MCore.Real.P02BehavioralAlignment.total_behavioral_alignment_to_exact T

#print axioms P02.LANE4.StructureBundle.r1r3Structure
#print axioms P02.LANE4.StructureBundle.r2Structure
#print axioms P02.LANE4.StructureBundle.r4Structure
#print axioms P02.LANE4.StructureBundle.r5Structure
#print axioms P02.LANE4.StructureBundle.auxStructure
#print axioms P02.LANE4.StructureBundle.aux_plus_t10_to_exact

end StructureBundle
end LANE4
end P02
