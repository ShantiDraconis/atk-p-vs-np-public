import MCore.Real.P02DeterministicRejectionTableau
import MCore.Real.FailProofFiniteAttack

namespace MCore
namespace Real
namespace P02SemanticSelfSubstitution

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02DeterministicRejectionTableau

/-- Canonical encoded rejection tableau for candidate M on source input x,
using exactly M's own polynomial clock at x. -/
def rejectCode
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit
    (boundedRejectCircuit_DTM M x (M.timeBound x.length))

/-- Material semantics of the encoded rejection tableau. -/
theorem rejectCode_semantics
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATBits circuitBitEncoding (rejectCode M x) ↔
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = false := by
  unfold rejectCode
  rw [encoded_sat_equivalence]
  exact rejection_tableau_correctness M x (M.timeBound x.length)

/-- If M is correct on rejectCode M x, then the output bit on the encoded
rejection tableau is the Boolean complement of the output bit on x,
provided M halts on x at its own clock. -/
theorem correctAt_rejectCode_flip
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx :
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x))
    (hCorrect :
      M.CorrectAt
        (SATBits circuitBitEncoding)
        (rejectCode M x)) :
    (M.accepting
        (M.machine.run
          (M.timeBound (rejectCode M x).length)
          (initialTMConfig M.machine (rejectCode M x))).state = true) ↔
      (M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = false) := by
  rcases hCorrect with ⟨_, hiff⟩
  constructor
  · intro hacc
    exact (rejectCode_semantics M x).mp (hiff.mp hacc) |>.2
  · intro hrej
    exact hiff.mpr ((rejectCode_semantics M x).mpr ⟨hx, hrej⟩)

/-- Semantic closure is strictly weaker than literal self-code equality:
only M's observed acceptance bit must agree between x and rejectCode M x. -/
def SemanticClosureAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound (rejectCode M x).length)
        (initialTMConfig M.machine (rejectCode M x))).state =
    M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state

/-- A semantic collision already forces failure of correctness on rejectCode.
No literal fixed point x = rejectCode M x is required. -/
theorem semantic_closure_forces_failure
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx :
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x))
    (hclose : SemanticClosureAt M x) :
    ¬ M.CorrectAt
        (SATBits circuitBitEncoding)
        (rejectCode M x) := by
  intro hCorrect
  have hflip := correctAt_rejectCode_flip M x hx hCorrect
  unfold SemanticClosureAt at hclose
  cases hsrc :
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state with
  | false =>
      have hcodeFalse :
          M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state = false := by
        simpa [hsrc] using hclose
      have hcodeTrue := hflip.mpr hsrc
      simp_all
  | true =>
      have hcodeTrue :
          M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state = true := by
        simpa [hsrc] using hclose
      have hsrcFalse := hflip.mp hcodeTrue
      simp_all

/-- Own-clock halting predicate used to separate the trivial nonhalting
failure branch from the genuinely semantic branch. -/
def OwnClockHalts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

/-- Any own-clock nonhalting input already falsifies CorrectAt directly. -/
theorem nonhalting_input_forces_failure
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx : ¬ OwnClockHalts M x) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x := by
  intro hCorrect
  exact hx hCorrect.1

/-- Strong sufficient producer retained for comparison. It is not the exact
remaining frontier because candidates with a nonhalting input already fail
CorrectAt without any semantic collision. -/
def SemanticCollisionProducer : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      SemanticClosureAt M x

theorem semanticCollisionProducer_implies_universal_failure :
    SemanticCollisionProducer →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  intro M
  rcases H M with ⟨x, hx, hclose⟩
  refine ⟨rejectCode M x, ?_⟩
  exact semantic_closure_forces_failure M x hx hclose


/-- Exact residual after discharging the trivial nonhalting branch:
only candidates that halt at their own clock on every input need a semantic
collision. -/
def TotalClockSemanticCollision : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ x : BitString, OwnClockHalts M x) →
      ∃ x : BitString, SemanticClosureAt M x


/-- Observable Boolean produced by M on input x at M's own clock. -/
def observedBit
    (M : PolyDTMCandidate)
    (x : BitString) : Bool :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state

theorem semanticClosureAt_iff_observed_eq
    (M : PolyDTMCandidate)
    (x : BitString) :
    SemanticClosureAt M x ↔
      observedBit M (rejectCode M x) = observedBit M x := by
  rfl

/-- For Booleans, failure of semantic closure is exactly a bit flip. -/
theorem not_semanticClosureAt_iff_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    ¬ SemanticClosureAt M x ↔
      observedBit M (rejectCode M x) = !(observedBit M x) := by
  rw [semanticClosureAt_iff_observed_eq]
  cases h0 : observedBit M x <;>
    cases h1 : observedBit M (rejectCode M x) <;>
    simp_all

/-- Global absence of collisions is exactly global alternation along rejectCode. -/
theorem no_semantic_collision_iff_global_flip
    (M : PolyDTMCandidate) :
    (¬ ∃ x : BitString, SemanticClosureAt M x) ↔
      (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) := by
  constructor
  · intro H x
    exact (not_semanticClosureAt_iff_flip M x).mp (by
      intro hx
      exact H ⟨x, hx⟩)
  · intro H hex
    rcases hex with ⟨x, hx⟩
    have hflip := H x
    have hnot := (not_semanticClosureAt_iff_flip M x).mpr hflip
    exact hnot hx

/-- Exact anti-alternation formulation of the total-clock residual. -/
def TotalClockAntiAlternation : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ x : BitString, OwnClockHalts M x) →
      ¬ (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x))

theorem totalClockCollision_iff_antiAlternation :
    TotalClockSemanticCollision ↔ TotalClockAntiAlternation := by
  constructor
  · intro H M htotal hflip
    rcases H M htotal with ⟨x, hclose⟩
    have hnot := (not_semanticClosureAt_iff_flip M x).mpr (hflip x)
    exact hnot hclose
  · intro H M htotal
    by_contra hnone
    have hflip :=
      (no_semantic_collision_iff_global_flip M).mp hnone
    exact H M htotal hflip


/-- Negative control: a finite Boolean state space can alternate forever
without a one-step collision. Therefore Boolean finiteness/pigeonhole alone
cannot prove TotalClockAntiAlternation. -/
def toyFlipMap (b : Bool) : Bool := !b

def toyObservedBit (b : Bool) : Bool := b

theorem toy_global_flip :
    ∀ b : Bool,
      toyObservedBit (toyFlipMap b) = !(toyObservedBit b) := by
  intro b
  cases b <;> rfl

theorem toy_no_semantic_collision :
    ¬ ∃ b : Bool,
      toyObservedBit (toyFlipMap b) = toyObservedBit b := by
  rintro ⟨b, hb⟩
  cases b <;> simp [toyFlipMap, toyObservedBit] at hb

/-- Under a global flip law, a literal fixed point of the transform is
impossible. Any successful anti-alternation proof must therefore use a
property stronger than existence of x with rejectCode M x = x. -/
theorem global_flip_no_literal_fixed_point
    (M : PolyDTMCandidate)
    (hflip :
      ∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) :
    ∀ x : BitString, rejectCode M x ≠ x := by
  intro x hfix
  have h := hflip x
  rw [hfix] at h
  cases hb : observedBit M x <;> simp_all


/-!
KERNEL PROBE: expose the specific rejectCode invariant that could break
global alternation. These are deliberately stated as propositions, not assumed
as axioms. The gate should reveal which reductions are kernel-derivable from
the current tableau construction.
-/

/-- Candidate invariant A: the encoded rejection transform does not increase
the candidate's own clock requirement. -/
def RejectCodeClockNonexpansive : Prop :=
  ∀ M : PolyDTMCandidate, ∀ x : BitString,
    M.timeBound (rejectCode M x).length ≤ M.timeBound x.length

/-- Candidate invariant B: rejectCode is idempotent. This is intentionally
separated because literal idempotence would be much stronger than semantic
closure. -/
def RejectCodeIdempotent : Prop :=
  ∀ M : PolyDTMCandidate, ∀ x : BitString,
    rejectCode M (rejectCode M x) = rejectCode M x

/-- Candidate invariant C: own-clock halting is preserved by rejectCode. -/
def RejectCodePreservesOwnClockHalts : Prop :=
  ∀ M : PolyDTMCandidate, ∀ x : BitString,
    OwnClockHalts M x → OwnClockHalts M (rejectCode M x)


/-- On the total-clock branch, preservation of halting by rejectCode is
automatic and therefore carries zero additional information. -/
theorem totalClock_trivially_preserves_rejectCode_halting
    (M : PolyDTMCandidate)
    (htotal : ∀ y : BitString, OwnClockHalts M y) :
    ∀ x : BitString,
      OwnClockHalts M x → OwnClockHalts M (rejectCode M x) := by
  intro x _
  exact htotal (rejectCode M x)

/-- PolynomialTimeBound is only an upper-bound condition; it does not impose
monotonicity on the clock function. -/
def nonmonotonePolyClock : TimeBound :=
  fun n => if n = 0 then 1 else 0

theorem nonmonotonePolyClock_poly :
    PolynomialTimeBound nonmonotonePolyClock := by
  refine ⟨1, 0, ?_⟩
  intro n
  simp [nonmonotonePolyClock]
  split <;> simp_all

theorem nonmonotonePolyClock_not_monotone :
    ¬ (∀ a b : Nat, a ≤ b →
      nonmonotonePolyClock a ≤ nonmonotonePolyClock b) := by
  intro H
  have h := H 0 1 (by omega)
  simp [nonmonotonePolyClock] at h

/-- Exact execution-level invariant requested from the kernel: on total-clock
machines, some source x must make the rejectCode observation collapse to the
same output bit. This is intentionally phrased through concrete run/clock
semantics rather than as TotalClockAntiAlternation itself. -/
def RejectCodeRunCollapse : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        M.accepting
            (M.machine.run
              (M.timeBound (rejectCode M x).length)
              (initialTMConfig M.machine (rejectCode M x))).state =
          M.accepting
            (M.machine.run
              (M.timeBound x.length)
              (initialTMConfig M.machine x)).state

theorem rejectCodeRunCollapse_iff_totalClockSemanticCollision :
    RejectCodeRunCollapse ↔ TotalClockSemanticCollision := by
  rfl

theorem rejectCodeRunCollapse_implies_antiAlternation :
    RejectCodeRunCollapse → TotalClockAntiAlternation := by
  intro H
  exact totalClockCollision_iff_antiAlternation.mp
    (rejectCodeRunCollapse_iff_totalClockSemanticCollision.mp H)

/-- If literal idempotence were available, it would immediately contradict
global flip at rejectCode x. This theorem isolates that route without claiming
idempotence is true. -/
theorem idempotence_breaks_global_flip
    (M : PolyDTMCandidate)
    (hid : ∀ x : BitString,
      rejectCode M (rejectCode M x) = rejectCode M x) :
    ¬ (∀ x : BitString,
      observedBit M (rejectCode M x) = !(observedBit M x)) := by
  intro hflip
  let x0 : BitString := []
  have h1 := hflip (rejectCode M x0)
  rw [hid x0] at h1
  cases hb : observedBit M (rejectCode M x0) <;> simp_all


/-- Concrete counterexample to universal idempotence of rejectCode. -/
theorem rejectCode_not_idempotent_on_alwaysReject :
    rejectCode
        FailProofFiniteAttack.alwaysRejectCandidate
        (rejectCode FailProofFiniteAttack.alwaysRejectCandidate []) ≠
      rejectCode FailProofFiniteAttack.alwaysRejectCandidate [] := by
  native_decide

theorem rejectCodeIdempotent_refuted :
    ¬ RejectCodeIdempotent := by
  intro H
  exact rejectCode_not_idempotent_on_alwaysReject
    (H FailProofFiniteAttack.alwaysRejectCandidate [])

/-- This is the exact clock-collapse shape suggested for the kernel to expose.
It does not assert that the current tableau construction proves it. -/
def RejectCodeClockCollapse : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        M.timeBound (rejectCode M x).length ≤ M.timeBound x.length ∧
        SemanticClosureAt M x

theorem rejectCodeClockCollapse_implies_runCollapse :
    RejectCodeClockCollapse → RejectCodeRunCollapse := by
  intro H M htotal
  rcases H M htotal with ⟨x, _, hclose⟩
  exact ⟨x, hclose⟩

theorem totalClockSemanticCollision_implies_universal_failure :
    TotalClockSemanticCollision →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  intro M
  classical
  by_cases htotal : ∀ x : BitString, OwnClockHalts M x
  · rcases H M htotal with ⟨x, hclose⟩
    refine ⟨rejectCode M x, ?_⟩
    exact semantic_closure_forces_failure M x (htotal x) hclose
  · push_neg at htotal
    rcases htotal with ⟨x, hx⟩
    exact ⟨x, nonhalting_input_forces_failure M x hx⟩

/-- Equivalent split form of the remaining sufficient material. -/
def TerminalSemanticSplit : Prop :=
  ∀ M : PolyDTMCandidate,
    (∃ x : BitString, ¬ OwnClockHalts M x) ∨
      (∃ x : BitString, OwnClockHalts M x ∧ SemanticClosureAt M x)

theorem totalClockSemanticCollision_implies_terminalSplit :
    TotalClockSemanticCollision → TerminalSemanticSplit := by
  intro H M
  classical
  by_cases htotal : ∀ x : BitString, OwnClockHalts M x
  · right
    rcases H M htotal with ⟨x, hclose⟩
    exact ⟨x, htotal x, hclose⟩
  · left
    push_neg at htotal
    exact htotal

theorem terminalSplit_implies_universal_failure :
    TerminalSemanticSplit →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H M
  rcases H M with hnonhalt | hcollision
  · rcases hnonhalt with ⟨x, hx⟩
    exact ⟨x, nonhalting_input_forces_failure M x hx⟩
  · rcases hcollision with ⟨x, hx, hclose⟩
    exact ⟨rejectCode M x, semantic_closure_forces_failure M x hx hclose⟩

#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCode_semantics
#print axioms MCore.Real.P02SemanticSelfSubstitution.correctAt_rejectCode_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.semantic_closure_forces_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.semanticCollisionProducer_implies_universal_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.nonhalting_input_forces_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.totalClockSemanticCollision_implies_universal_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.not_semanticClosureAt_iff_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.no_semantic_collision_iff_global_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.totalClockCollision_iff_antiAlternation
#print axioms MCore.Real.P02SemanticSelfSubstitution.toy_no_semantic_collision
#print axioms MCore.Real.P02SemanticSelfSubstitution.global_flip_no_literal_fixed_point
#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCodeRunCollapse_iff_totalClockSemanticCollision
#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCodeRunCollapse_implies_antiAlternation
#print axioms MCore.Real.P02SemanticSelfSubstitution.idempotence_breaks_global_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCode_not_idempotent_on_alwaysReject
#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCodeIdempotent_refuted
#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCodeClockCollapse_implies_runCollapse
#print axioms MCore.Real.P02SemanticSelfSubstitution.totalClock_trivially_preserves_rejectCode_halting
#print axioms MCore.Real.P02SemanticSelfSubstitution.nonmonotonePolyClock_poly
#print axioms MCore.Real.P02SemanticSelfSubstitution.nonmonotonePolyClock_not_monotone
#print axioms MCore.Real.P02SemanticSelfSubstitution.terminalSplit_implies_universal_failure

end P02SemanticSelfSubstitution
end Real
end MCore
