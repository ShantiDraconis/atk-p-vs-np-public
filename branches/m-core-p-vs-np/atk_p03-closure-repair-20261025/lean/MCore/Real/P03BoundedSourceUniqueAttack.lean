import MCore.Real.P03UniformRangeDecoder
import MCore.Real.FailProofFiniteAttack

namespace MCore
namespace Real
namespace P03BoundedSourceUniqueAttack

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open FailProofFiniteAttack
open P03UniformRangeDecoder

/--
A deliberately simple total polynomial candidate with an injective declared
clock.  The machine itself is the already-defined one-state halting rejector;
only the declared clock is strengthened from 0 to n+1 so source lengths can be
recovered from equal clock values.
-/
def injectiveRejectCandidate : PolyDTMCandidate :=
  { stateCount := 0
    machine := alwaysRejectMachine
    blank_none := rfl
    accepting := fun _ => false
    timeBound := fun n => n + 1
    time_poly := by
      refine ⟨1, 1, ?_⟩
      intro n
      simp [CanonicalFinalProof.PolynomialTimeBound] }

/-- Its declared time bound is injective in the input length. -/
theorem injectiveRejectCandidate_time_injective :
    Function.Injective injectiveRejectCandidate.timeBound := by
  intro a b h
  simpa [injectiveRejectCandidate] using h

/-- The underlying machine is halting already at the initial state, hence it is
total at every positive declared clock. -/
theorem injectiveRejectCandidate_total :
    DeclaredClockTotal injectiveRejectCandidate := by
  intro x
  simp [DeclaredClockTotal, DeclaredHalts, injectiveRejectCandidate,
    alwaysRejectMachine, initialTMConfig, TM.HaltsWithin, TM.run]

/--
The remaining step for BoundedSourceUnique is now isolated cleanly:
show that any bounded source candidate over this real range must have the same
source length as the genuine source.  Once lengths agree, both decoders use the
same clock and the already-certified source decoder forces equality of sources.
-/
def InjectiveRejectLengthUniqueness : Prop :=
  ∀ (x : BitString)
    (C : BoundedSourceCandidate
      injectiveRejectCandidate
      (P02TableauDynamics.R_M
        injectiveRejectCandidate
        injectiveRejectCandidate_total
        x)),
    C.source.length = x.length

theorem length_uniqueness_closes_bounded_source_unique
    (hLen : InjectiveRejectLengthUniqueness) :
    BoundedSourceUnique
      injectiveRejectCandidate
      injectiveRejectCandidate_total := by
  intro x C
  have hlen : C.source.length = x.length := hLen x C
  have hCandidate := C.decodes
  have hGenuine :=
    (genuineSourceCandidate
      injectiveRejectCandidate
      injectiveRejectCandidate_total
      x).decodes
  rw [hlen] at hCandidate
  rw [hGenuine] at hCandidate
  exact (Option.some.inj hCandidate).symm

#print axioms MCore.Real.P03BoundedSourceUniqueAttack.injectiveRejectCandidate_time_injective
#print axioms MCore.Real.P03BoundedSourceUniqueAttack.injectiveRejectCandidate_total

end P03BoundedSourceUniqueAttack
end Real
end MCore
