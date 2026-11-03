import MCore.Real.P02SemanticSelfSubstitution

namespace MCore
namespace Real
namespace P02RejectionImageEscape

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfSubstitution

theorem totalClock_globalFlip_iff_correctOnRejectImage
    (M : PolyDTMCandidate)
    (hTotal : ∀ y : BitString, OwnClockHalts M y) :
    (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) ↔
      (∀ x : BitString,
        M.CorrectAt (SATBits circuitBitEncoding) (rejectCode M x)) := by
  constructor
  · intro hFlip x
    refine ⟨hTotal (rejectCode M x), ?_⟩
    have hSem := rejectCode_semantics M x
    have hx := hTotal x
    have hF := hFlip x
    unfold observedBit at hF
    constructor
    · intro hAcc
      have hSrcFalse :
          M.accepting
              (M.machine.run
                (M.timeBound x.length)
                (initialTMConfig M.machine x)).state = false := by
        cases hsrc :
            M.accepting
              (M.machine.run
                (M.timeBound x.length)
                (initialTMConfig M.machine x)).state <;>
          cases hdst :
            M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state <;>
          simp_all
      exact (hSem.mpr ⟨hx, hSrcFalse⟩)
    · intro hSat
      have hSrcFalse := (hSem.mp hSat).2
      cases hsrc :
          M.accepting
            (M.machine.run
              (M.timeBound x.length)
              (initialTMConfig M.machine x)).state <;>
        cases hdst :
          M.accepting
            (M.machine.run
              (M.timeBound (rejectCode M x).length)
              (initialTMConfig M.machine (rejectCode M x))).state <;>
        simp_all
  · intro hCorrect x
    have h :=
      correctAt_rejectCode_flip M x (hTotal x) (hCorrect x)
    unfold observedBit
    cases hsrc :
        M.accepting
          (M.machine.run
            (M.timeBound x.length)
            (initialTMConfig M.machine x)).state <;>
      cases hdst :
        M.accepting
          (M.machine.run
            (M.timeBound (rejectCode M x).length)
            (initialTMConfig M.machine (rejectCode M x))).state <;>
      simp_all

def RejectImageEscape : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        ¬ M.CorrectAt (SATBits circuitBitEncoding) (rejectCode M x)

theorem rejectImageEscape_iff_totalClockAntiAlternation :
    RejectImageEscape ↔ TotalClockAntiAlternation := by
  constructor
  · intro H M hTotal hFlip
    rcases H M hTotal with ⟨x, hFail⟩
    have hCorrectImage :=
      (totalClock_globalFlip_iff_correctOnRejectImage M hTotal).mp hFlip
    exact hFail (hCorrectImage x)
  · intro H M hTotal
    by_contra hNoEscape
    push_neg at hNoEscape
    have hFlip :=
      (totalClock_globalFlip_iff_correctOnRejectImage M hTotal).mpr hNoEscape
    exact H M hTotal hFlip

theorem rejectImageEscape_implies_universalFailure :
    RejectImageEscape →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  exact totalClockSemanticCollision_implies_universal_failure
    (totalClockCollision_iff_antiAlternation.mpr
      (rejectImageEscape_iff_totalClockAntiAlternation.mp H))


/-!
T7-FINAL-CLOSURE

Terminal signature truncation. Endpoint, Gap, Habitant and Inhabitant are one
definitionally identical proposition. No additional parameter is opened below
this frontier.
-/

abbrev CandidateCodeSemanticFixedPoint : Prop := RejectImageEscape
abbrev Endpoint : Prop := CandidateCodeSemanticFixedPoint
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem endpoint_iff_gap : Endpoint ↔ Gap := Iff.rfl
theorem endpoint_iff_habitant : Endpoint ↔ Habitant := Iff.rfl
theorem endpoint_iff_inhabitant : Endpoint ↔ Inhabitant := Iff.rfl
theorem endpoint_iff_rejectImageEscape : Endpoint ↔ RejectImageEscape := Iff.rfl

theorem terminal_cycle :
    (Endpoint ↔ Gap) ∧
    (Gap ↔ Habitant) ∧
    (Habitant ↔ Inhabitant) ∧
    (Inhabitant ↔ Endpoint) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- All four terminal names carry exactly the same inhabitance obligation. -/
theorem terminal_inhabitance_exact :
    Endpoint ↔ Gap ∧ Habitant ∧ Inhabitant := by
  constructor
  · intro h
    exact ⟨h, h, h⟩
  · rintro ⟨h, _, _⟩
    exact h

/--
A literal rejectCode fixed point would be sufficient at a concrete point,
but is not available as a universal shortcut.
-/
theorem literal_fixed_point_closes_at
    (M : PolyDTMCandidate)
    (hTotal : ∀ y : BitString, OwnClockHalts M y)
    (x : BitString)
    (hfix : rejectCode M x = x) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) (rejectCode M x) := by
  apply semantic_closure_forces_failure M x (hTotal x)
  unfold SemanticClosureAt
  rw [hfix]

theorem global_flip_blocks_literal_diagonal
    (M : PolyDTMCandidate)
    (hFlip :
      ∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) :
    ∀ x : BitString, rejectCode M x ≠ x :=
  global_flip_no_literal_fixed_point M hFlip

theorem no_literal_idempotence_shortcut :
    ¬ RejectCodeIdempotent :=
  rejectCodeIdempotent_refuted

/--
Exact terminal mincut. Producing the inhabitant of any terminal alias is
definitionally identical to producing RejectImageEscape itself.
-/
theorem terminal_inhabitant_iff_rejectImageEscape :
    Inhabitant ↔ RejectImageEscape :=
  Iff.rfl

theorem endpoint_closes_universalFailure :
    Endpoint → UniversalFailure (SATBits circuitBitEncoding) :=
  rejectImageEscape_implies_universalFailure

#print axioms MCore.Real.P02RejectionImageEscape.totalClock_globalFlip_iff_correctOnRejectImage
#print axioms MCore.Real.P02RejectionImageEscape.rejectImageEscape_iff_totalClockAntiAlternation
#print axioms MCore.Real.P02RejectionImageEscape.rejectImageEscape_implies_universalFailure
#print axioms MCore.Real.P02RejectionImageEscape.terminal_cycle
#print axioms MCore.Real.P02RejectionImageEscape.terminal_inhabitance_exact
#print axioms MCore.Real.P02RejectionImageEscape.literal_fixed_point_closes_at
#print axioms MCore.Real.P02RejectionImageEscape.global_flip_blocks_literal_diagonal
#print axioms MCore.Real.P02RejectionImageEscape.no_literal_idempotence_shortcut
#print axioms MCore.Real.P02RejectionImageEscape.terminal_inhabitant_iff_rejectImageEscape
#print axioms MCore.Real.P02RejectionImageEscape.endpoint_closes_universalFailure

end P02RejectionImageEscape
end Real
end MCore
