import MCore.Real.P02Lane4SemanticGate
import MCore.Attack.CanonicalTerminalProducer
import MCore.Real.P01PostMinCutClosure
import P02.LANE4.StructureBundle

import MCore.Real.P02OperatorKernel
import MCore.Real.P02FinalCompression
import MCore.Real.P02UniversalLowerBound
import MCore.Real.P02CanonicalClockReduction
import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.P02ExactDiagonalFrontier
import MCore.Real.P02BehavioralAlignment
import MCore.Real.P02KleeneKernel
import MCore.Real.P02EffectiveAlignment
import MCore.Real.P02UniversalLowerBoundMaster

namespace P02
namespace LANE4
namespace AdvancedCertificateReuse

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.CanonicalSATBoundary
open MCore.Real.CanonicalCircuitBits
open MCore.Real.P02OperatorKernel
open MCore.Real.P02UniversalLowerBound
open MCore.Real.P02CanonicalClockReduction
open MCore.Real.P02UniversalFailureMinCut
open MCore.Real.P02ExactDiagonalFrontier
open MCore.Real.P02BehavioralAlignment
open MCore.Real.P02KleeneKernel
open MCore.Real.P02EffectiveAlignment
open MCore.Real.P02UniversalLowerBoundMaster
open MCore.Real.P01PostMinCutClosure
open MCore.Real.P02Lane4SemanticGate

/-- Fixed canonical SAT target shared by the frozen P01 side and all
current P02 normal forms. -/
abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- Port of the historical G2.1/G21 pointwise target into the current
canonical model. -/
def G21Pointwise : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ candidate.CorrectAt SATTarget x

theorem g21_iff_universal_failure :
    G21Pointwise ↔ UniversalFailure SATTarget :=
  Iff.rfl

theorem g21_iff_universal_lower_bound :
    G21Pointwise ↔ P02UniversalLowerBound.UniversalSATLowerBound := by
  rw [g21_iff_universal_failure]
  exact P02UniversalLowerBound.universalSATLowerBound_iff_universalFailure.symm

theorem g21_iff_not_in_p :
    G21Pointwise ↔ ¬ InP SATTarget := by
  rw [g21_iff_universal_lower_bound]
  exact P02UniversalLowerBound.universalSATLowerBound_iff_notInP

theorem g21_iff_p02_operator :
    G21Pointwise ↔ Nonempty P02OperatorKernel.CanonicalSATP02Producer := by
  rw [g21_iff_not_in_p]
  exact P02OperatorKernel.canonicalSATProducer_iff_notInP.symm

theorem g21_iff_normalized_adversary :
    G21Pointwise ↔ Nonempty P02CanonicalClockReduction.NormalizedAdversary := by
  rw [g21_iff_universal_lower_bound]
  exact P02CanonicalClockReduction.normalizedAdversary_iff_universalSATLowerBound.symm


/-- Explicit non-rfl transport requested by the terminal audit.  This consumes
UniversalSATLowerBound; it does not manufacture the lower-bound witness. -/
theorem g21Pointwise_of_lowerBound
    (h : P02UniversalLowerBound.UniversalSATLowerBound) :
    G21Pointwise := by
  exact g21_iff_universal_lower_bound.mpr h

/-- Reverse transport, making the exact equivalence visible to audit tooling. -/
theorem lowerBound_of_g21Pointwise
    (h : G21Pointwise) :
    P02UniversalLowerBound.UniversalSATLowerBound := by
  exact g21_iff_universal_lower_bound.mp h

/-- A direct genuine G21 inhabitant closes the internal endpoint without T10.
Therefore T10 is a sufficient producer route, not a second mandatory terminal. -/
theorem g21_closes_internal_endpoint
    (h : G21Pointwise) :
    PneqNP := by
  exact P02UniversalLowerBoundMaster.universal_lower_bound_closes_internal
    (lowerBound_of_g21Pointwise h)

/-- The frozen Claim1--7 bundle is a useful certified source object, but
the existing semantic gate proves that a bridge from it to P02 is exactly as
strong as the official target.  This is a firewall, not a producer. -/
theorem claim_bundle_bridge_iff_g21 :
    MCore.Real.P02Lane4SemanticGate.T10SemanticBridge ↔ G21Pointwise := by
  rw [MCore.Real.P02Lane4SemanticGate.t10SemanticBridge_iff_officialTarget]
  exact g21_iff_universal_lower_bound.symm

theorem claim_bundle_is_inhabited :
    MCore.Real.P02Lane4SemanticGate.CandidateRoot :=
  MCore.Real.P02Lane4SemanticGate.candidateRoot_inhabited

/-- The entire SAT-in-NP side is already kernel-connected in the current
branch and should be reused rather than reopened. -/
theorem p01_side_closed :
    InNP SATTarget :=
  P01PostMinCutClosure.canonical_sat_in_np_closed

/-- G2.2 is a consumer/equivalent form, not an independent producer. -/
def G22Contradiction : Prop :=
  ∀ realization : PolyDTMRealization SATTarget, False

theorem g22_iff_not_in_p :
    G22Contradiction ↔ ¬ InP SATTarget := by
  constructor
  · intro h hP
    rcases hP with ⟨R⟩
    exact h R
  · intro h R
    exact h ⟨R⟩

theorem g21_iff_g22 :
    G21Pointwise ↔ G22Contradiction := by
  rw [g21_iff_not_in_p, g22_iff_not_in_p]

/-- Any genuine G21 producer now forms the exact canonical terminal witness
because P01/G1 is already closed. -/
def canonicalNotInPWitnessOfG21
    (h : G21Pointwise) :
    MCore.Attack.CanonicalNotInPWitness :=
  { language := SATTarget
    in_np := p01_side_closed
    not_in_p := g21_iff_not_in_p.mp h }

/-- Historical terminal accounting, ported to the current P01-closed branch:
the only remaining mathematical producer is G21. -/
abbrev CURRENT_FINAL_OPEN_MATH : Prop :=
  G21Pointwise

/--
All post-T10 targets that were already present in the repository but were not
previously exposed as one LANE4 chain.

This structure contains only theorem-level transports.  It does not inhabit
T10 or any lower-bound producer.
-/
structure ReusedTerminalChain where
  exact_to_failure :
    TotalExactDiagonalProducer →
      UniversalFailure P02UniversalFailureMinCut.CanonicalSAT

  failure_to_lower_bound :
    UniversalFailure P02UniversalFailureMinCut.CanonicalSAT →
      P02UniversalLowerBound.UniversalSATLowerBound

  lower_bound_to_operator :
    P02UniversalLowerBound.UniversalSATLowerBound →
      Nonempty P02OperatorKernel.CanonicalSATP02Producer

  lower_bound_to_not_in_p :
    P02UniversalLowerBound.UniversalSATLowerBound →
      ¬ InP (SATBits circuitBitEncoding)

  lower_bound_to_normalized :
    P02UniversalLowerBound.UniversalSATLowerBound →
      Nonempty P02CanonicalClockReduction.NormalizedAdversary

  lower_bound_to_operational :
    P02UniversalLowerBound.UniversalSATLowerBound →
      ∀ M : PolyDTMCandidate,
        ∃ x : BitString,
          ¬ P02UniversalLowerBound.HaltsAtDeclaredBound M x ∨
            P02UniversalLowerBound.SemanticMismatch M x

/-- Existing repository theorems populate the entire post-T10 chain. -/
def reusedTerminalChain : ReusedTerminalChain where
  exact_to_failure :=
    P02ExactDiagonalFrontier.total_exact_diagonal_implies_universal_failure

  failure_to_lower_bound := fun h =>
    P02UniversalLowerBound.universalSATLowerBound_iff_universalFailure.mpr h

  lower_bound_to_operator := fun h =>
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_p02_operator.mp h

  lower_bound_to_not_in_p := fun h =>
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_not_in_p.mp h

  lower_bound_to_normalized := fun h =>
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_normalized_adversary.mp h

  lower_bound_to_operational := fun h =>
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_operational.mp h

/-- Exact diagonal production reaches every already-certified terminal normal
form without any new open bridge. -/
theorem exact_diagonal_to_universal_lower_bound
    (B : TotalExactDiagonalProducer) :
    P02UniversalLowerBoundMaster.UNIVERSAL_LOWER_BOUND := by
  apply P02UniversalLowerBound.universalSATLowerBound_iff_universalFailure.mpr
  exact P02ExactDiagonalFrontier.total_exact_diagonal_implies_universal_failure B

theorem exact_diagonal_to_p02_operator
    (B : TotalExactDiagonalProducer) :
    Nonempty P02OperatorKernel.CanonicalSATP02Producer := by
  exact
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_p02_operator.mp
      (exact_diagonal_to_universal_lower_bound B)

theorem exact_diagonal_to_universal_counterexample
    (B : TotalExactDiagonalProducer) :
    Nonempty P02UniversalFailureMinCut.UniversalCounterexampleProducer := by
  apply P02UniversalFailureMinCut.producer_iff_universal_failure.mpr
  exact P02ExactDiagonalFrontier.total_exact_diagonal_implies_universal_failure B

theorem exact_diagonal_to_normalized_adversary
    (B : TotalExactDiagonalProducer) :
    Nonempty P02CanonicalClockReduction.NormalizedAdversary := by
  exact
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_normalized_adversary.mp
      (exact_diagonal_to_universal_lower_bound B)

theorem exact_diagonal_to_not_in_p
    (B : TotalExactDiagonalProducer) :
    ¬ InP (SATBits circuitBitEncoding) := by
  exact
    P02UniversalLowerBoundMaster.universal_lower_bound_iff_not_in_p.mp
      (exact_diagonal_to_universal_lower_bound B)

/-- T10 is now connected to the entire existing terminal chain.  This theorem
does not construct T10; it only proves that no structural gap remains after it.
-/
theorem t10_to_exact
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    TotalExactDiagonalProducer :=
  MCore.Real.P02BehavioralAlignment.total_behavioral_alignment_to_exact T

theorem t10_to_universal_lower_bound
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    P02UniversalLowerBoundMaster.UNIVERSAL_LOWER_BOUND :=
  exact_diagonal_to_universal_lower_bound (t10_to_exact T)

theorem t10_to_p02_operator
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    Nonempty P02OperatorKernel.CanonicalSATP02Producer :=
  exact_diagonal_to_p02_operator (t10_to_exact T)

theorem t10_to_not_in_p
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    ¬ InP (SATBits circuitBitEncoding) :=
  exact_diagonal_to_not_in_p (t10_to_exact T)

/-- Existing P01 closure consumes the exact lower-bound object.  This remains
an internal repository endpoint theorem, not a claim that T10 is inhabited. -/
theorem t10_closes_internal_endpoint
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    PneqNP :=
  P02UniversalLowerBoundMaster.universal_lower_bound_closes_internal
    (t10_to_universal_lower_bound T)

/-- Alternative constructive route already present in the repository:
UniformEffectiveCoverage is sufficient for the same lower-bound endpoint.
It remains independently OPEN_MATH unless inhabited. -/
theorem effective_coverage_to_same_terminal
    (U : P02EffectiveAlignment.UniformEffectiveCoverage) :
    P02UniversalLowerBoundMaster.UNIVERSAL_LOWER_BOUND :=
  P02UniversalLowerBoundMaster.effective_coverage_implies_universal_lower_bound U

/-- Explicit accounting boundary: both active constructive routes land in the
same terminal proposition; neither route is manufactured here. -/
structure OpenProducerInventory where
  behavioral_route :
    Prop := MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer
  effective_route :
    Type := P02EffectiveAlignment.UniformEffectiveCoverage

abbrev TERMINAL_OPEN_MATH : Prop :=
  P02UniversalLowerBoundMaster.FINAL_OPEN_MATH


/-- T10 reaches the historical/current G21 terminal target directly. -/
theorem t10_to_g21
    (T : MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer) :
    G21Pointwise := by
  apply g21_iff_universal_lower_bound.mpr
  exact t10_to_universal_lower_bound T

/-- Uniform effective coverage is a second genuine constructive entry point
into exactly the same G21 target. -/
theorem effective_coverage_to_g21
    (U : P02EffectiveAlignment.UniformEffectiveCoverage) :
    G21Pointwise := by
  apply g21_iff_universal_lower_bound.mpr
  exact effective_coverage_to_same_terminal U

/-- Normalized adversary is an exact normal form, not an additional frontier. -/
theorem normalized_route_iff_g21 :
    Nonempty P02CanonicalClockReduction.NormalizedAdversary ↔ G21Pointwise :=
  g21_iff_normalized_adversary.symm

#print axioms P02.LANE4.AdvancedCertificateReuse.claim_bundle_bridge_iff_g21
#print axioms P02.LANE4.AdvancedCertificateReuse.claim_bundle_is_inhabited
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_iff_universal_failure
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_iff_not_in_p
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_iff_p02_operator
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_iff_normalized_adversary
#print axioms P02.LANE4.AdvancedCertificateReuse.g21Pointwise_of_lowerBound
#print axioms P02.LANE4.AdvancedCertificateReuse.lowerBound_of_g21Pointwise
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_closes_internal_endpoint
#print axioms P02.LANE4.AdvancedCertificateReuse.p01_side_closed
#print axioms P02.LANE4.AdvancedCertificateReuse.g21_iff_g22
#print axioms P02.LANE4.AdvancedCertificateReuse.t10_to_g21
#print axioms P02.LANE4.AdvancedCertificateReuse.effective_coverage_to_g21
#print axioms P02.LANE4.AdvancedCertificateReuse.normalized_route_iff_g21
#print axioms P02.LANE4.AdvancedCertificateReuse.reusedTerminalChain
#print axioms P02.LANE4.AdvancedCertificateReuse.exact_diagonal_to_universal_lower_bound
#print axioms P02.LANE4.AdvancedCertificateReuse.exact_diagonal_to_p02_operator
#print axioms P02.LANE4.AdvancedCertificateReuse.exact_diagonal_to_universal_counterexample
#print axioms P02.LANE4.AdvancedCertificateReuse.exact_diagonal_to_normalized_adversary
#print axioms P02.LANE4.AdvancedCertificateReuse.t10_to_universal_lower_bound
#print axioms P02.LANE4.AdvancedCertificateReuse.t10_closes_internal_endpoint
#print axioms P02.LANE4.AdvancedCertificateReuse.effective_coverage_to_same_terminal

end AdvancedCertificateReuse
end LANE4
end P02
