import MCore.Real.PNPDiscovery.FiniteCandidateDescription
import MCore.Real.PNPDiscovery.UnaryListSerialization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction

/-- Correct codebook target after canonical-clock normalization: only the
finite normalized description is encoded. -/
structure NormalizedCandidateCodebook where
  encode : FiniteCandidateDescription → BitString
  decode : BitString → Option FiniteCandidateDescription
  roundTrip :
    ∀ D : FiniteCandidateDescription,
      decode (encode D) = some D

/-- Every total hardened candidate has a semantically equivalent normalized
finite description. -/
structure TotalCandidateFiniteReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  description : FiniteCandidateDescription := finiteDescription M
  accepts :
    ∀ x : BitString,
      DeclaredAccepts description.toCandidate x ↔
        DeclaredAccepts M x

noncomputable def totalCandidateFiniteReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    TotalCandidateFiniteReduction M hTotal :=
  { description := finiteDescription M
    accepts := finiteDescription_semantic_roundTrip_closed M hTotal }

/-- One fixed universal machine needs to simulate only normalized finite
descriptions. -/
structure NormalizedUniversalSimulator
    (C : NormalizedCandidateCodebook)
    (P : MachineInputPairing) where
  simulator : PolyDTMCandidate
  total : DeclaredClockTotal simulator
  correct :
    ∀ (D : FiniteCandidateDescription)
      (x : BitString),
      DeclaredAccepts simulator
          (P.pack (C.encode D) x) ↔
        DeclaredAccepts D.toCandidate x

/-- Polynomial overhead over the normalized candidate's explicit canonical
clock and finite code length. -/
structure NormalizedUniversalOverhead
    (C : NormalizedCandidateCodebook)
    (P : MachineInputPairing)
    (U : NormalizedUniversalSimulator C P) where
  coefficient : Nat
  exponent : Nat
  bound :
    ∀ (D : FiniteCandidateDescription)
      (x : BitString),
      U.simulator.timeBound
          (P.pack (C.encode D) x).length ≤
        coefficient *
          (D.clock x.length +
            (C.encode D).length +
            x.length + 1) ^ exponent

structure NormalizedUniversalInfrastructure where
  pairing : MachineInputPairing
  codebook : NormalizedCandidateCodebook
  universal :
    NormalizedUniversalSimulator codebook pairing
  overhead :
    NormalizedUniversalOverhead
      codebook pairing universal

def NormalizedUniversalInfrastructureGap : Prop :=
  Nonempty NormalizedUniversalInfrastructure

/-- The old all-PolyDTMCandidate codebook is not needed for total-candidate
diagonalization once normalization is available. -/
theorem totalCandidate_simulation_reduces_to_normalized
    (I : NormalizedUniversalInfrastructure)
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    DeclaredAccepts
        I.universal.simulator
        (I.pairing.pack
          (I.codebook.encode (finiteDescription M))
          x) ↔
      DeclaredAccepts M x := by
  exact
    (I.universal.correct (finiteDescription M) x).trans
      (finiteDescription_semantic_roundTrip_closed
        M hTotal x)

/-- Exact method frontier after clock normalization. -/
structure NormalizedSelfReferenceCompiler
    (C : NormalizedCandidateCodebook) where
  transform :
    (BitString → BitString) →
      FiniteCandidateDescription
  fixedPoint :
    ∀ F : BitString → BitString,
      ∃ D : FiniteCandidateDescription,
        C.decode
          (F (C.encode (transform F))) = some D ∧
        CandidateBehaviorEquivalent
          (transform F).toCandidate
          D.toCandidate

def NormalizedSelfReferenceCompilerGap : Prop :=
  ∃ C : NormalizedCandidateCodebook,
    Nonempty (NormalizedSelfReferenceCompiler C)

/-- Current exact method obligations. -/
structure CurrentSelfReferencePrerequisites where
  universal : NormalizedUniversalInfrastructure
  selfReference :
    NormalizedSelfReferenceCompiler universal.codebook

def CurrentSelfReferencePrerequisitesGap : Prop :=
  Nonempty CurrentSelfReferencePrerequisites

#print axioms MCore.Real.PNPDiscovery.totalCandidate_simulation_reduces_to_normalized

end PNPDiscovery
end Real
end MCore
