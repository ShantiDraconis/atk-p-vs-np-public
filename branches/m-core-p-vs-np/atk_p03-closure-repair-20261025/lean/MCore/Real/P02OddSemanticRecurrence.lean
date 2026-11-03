import MCore.Real.P02InvariantCore

namespace MCore
namespace Real
namespace P02OddSemanticRecurrence

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02InvariantCore

/-- Forward orbit of an endomorphism on canonical bitstrings. -/
def Orbit
    (R : BitString → BitString)
    (x0 : BitString) : Nat → BitString
  | 0 => x0
  | n + 1 => R (Orbit R x0 n)

/-- Equality as observed by one deterministic candidate. -/
def ObsEquiv
    (M : PolyDTMCandidate)
    (u v : BitString) : Prop :=
  DeclaredAccepts M u ↔ DeclaredAccepts M v

/--
Constructive odd-distance relation.  We use j = i + (2*d+1) instead of a
modulo side condition so the parity argument is transparent to the kernel.
-/
def OddGap (i j : Nat) : Prop :=
  ∃ d : Nat, j = i + (2 * d + 1)

theorem oddGap_lt
    {i j : Nat}
    (h : OddGap i j) :
    i < j := by
  rcases h with ⟨d, rfl⟩
  omega

theorem oddGap_ne
    {i j : Nat}
    (h : OddGap i j) :
    i ≠ j :=
  Nat.ne_of_lt (oddGap_lt h)


/--
An orbit has odd semantic recurrence when two points at odd distance are
indistinguishable by M.
-/
def OddSemanticRecurrence
    (M : PolyDTMCandidate)
    (R : BitString → BitString) : Prop :=
  ∃ x0 i j,
    OddGap i j ∧
    ObsEquiv M (Orbit R x0 i) (Orbit R x0 j)

/-- Two consecutive semantic flips restore the original observation. -/
theorem two_flips_restore
    {P : Nat → Prop}
    (hFlip : ∀ k, P (k + 1) ↔ ¬ P k)
    (k : Nat) :
    P (k + 2) ↔ P k := by
  have h1 := hFlip k
  have h2 := hFlip (k + 1)
  constructor
  · intro hk2
    have hn1 : ¬ P (k + 1) := h2.mp hk2
    by_contra hnk
    have hk1 : P (k + 1) := h1.mpr hnk
    exact hn1 hk1
  · intro hk
    have hn1 : ¬ P (k + 1) := by
      intro hk1
      exact (h1.mp hk1) hk
    exact h2.mpr hn1

/-- Odd many perfect flips negate the initial observation. -/
theorem odd_flips_negate
    {P : Nat → Prop}
    (hFlip : ∀ k, P (k + 1) ↔ ¬ P k)
    (i d : Nat) :
    P (i + (2 * d + 1)) ↔ ¬ P i := by
  induction d with
  | zero =>
      simpa using hFlip i
  | succ d ih =>
      have hRestore :=
        two_flips_restore hFlip (i + (2 * d + 1))
      have hStep :
          P (i + (2 * d + 1) + 2) ↔ ¬ P i := by
        exact hRestore.trans ih
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hStep

/--
If no adjacent pair is observationally equal, classical two-valued semantics
forces every edge to flip.
-/
theorem no_adjacent_equiv_implies_flip
    {M : PolyDTMCandidate}
    {R : BitString → BitString}
    {x0 : BitString}
    (hNo :
      ∀ k,
        ¬ ObsEquiv M (Orbit R x0 k) (Orbit R x0 (k + 1))) :
    ∀ k,
      DeclaredAccepts M (Orbit R x0 (k + 1)) ↔
        ¬ DeclaredAccepts M (Orbit R x0 k) := by
  classical
  intro k
  let A : Prop := DeclaredAccepts M (Orbit R x0 k)
  let B : Prop := DeclaredAccepts M (Orbit R x0 (k + 1))
  have hne : ¬ (A ↔ B) := by
    simpa [A, B, ObsEquiv] using hNo k
  constructor
  · intro hB hA
    apply hne
    constructor
    · intro _
      exact hB
    · intro _
      exact hA
  · intro hnA
    by_contra hnB
    apply hne
    constructor
    · intro hA
      exact False.elim (hnA hA)
    · intro hB
      exact False.elim (hnB hB)

/--
Odd semantic recurrence forces at least one adjacent invariant edge.
This is the pure finite/parity part of the argument and contains no P/NP
endpoint.
-/
theorem oddRecurrence_implies_adjacent
    {M : PolyDTMCandidate}
    {R : BitString → BitString}
    (hOdd : OddSemanticRecurrence M R) :
    ∃ z : BitString, ObsEquiv M (R z) z := by
  classical
  rcases hOdd with ⟨x0, i, j, ⟨d, hj⟩, hEq⟩
  by_contra hNone
  have hNo :
      ∀ k,
        ¬ ObsEquiv M (Orbit R x0 k) (Orbit R x0 (k + 1)) := by
    intro k hObs
    apply hNone
    refine ⟨Orbit R x0 k, ?_⟩
    have hObs' :
        ObsEquiv M (Orbit R x0 (k + 1)) (Orbit R x0 k) := by
      exact hObs.symm
    simpa [Orbit] using hObs'
  have hFlip :=
    no_adjacent_equiv_implies_flip
      (M := M) (R := R) (x0 := x0) hNo
  have hNeg :
      DeclaredAccepts M (Orbit R x0 (i + (2 * d + 1))) ↔
        ¬ DeclaredAccepts M (Orbit R x0 i) :=
    odd_flips_negate
      (P := fun k => DeclaredAccepts M (Orbit R x0 k))
      hFlip i d
  have hSame :
      DeclaredAccepts M (Orbit R x0 i) ↔
        DeclaredAccepts M (Orbit R x0 (i + (2 * d + 1))) := by
    simpa [hj, ObsEquiv] using hEq
  by_cases hAi : DeclaredAccepts M (Orbit R x0 i)
  · have hAj :
        DeclaredAccepts M (Orbit R x0 (i + (2 * d + 1))) :=
      hSame.mp hAi
    exact (hNeg.mp hAj) hAi
  · have hAj :
        DeclaredAccepts M (Orbit R x0 (i + (2 * d + 1))) :=
      hNeg.mpr hAi
    exact hAi (hSame.mpr hAj)

/-- Recurrence specialized to the real complemented Cook--Levin reducer. -/
def TotalOddSemanticRecurrence : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    OddSemanticRecurrence M
      (complementSemanticReduction M hTotal).reduce

/--
The recurrence principle is sufficient to inhabit the exact P02 invariant
producer.  All mathematical content is isolated in TotalOddSemanticRecurrence.
-/
noncomputable def oddRecurrence_to_invariantProducer
    (H : TotalOddSemanticRecurrence) :
    TotalCandidateInvariantProducer := by
  classical
  let pick :
      ∀ (M : PolyDTMCandidate)
        (hTotal : DeclaredClockTotal M),
        BitString :=
    fun M hTotal =>
      Classical.choose
        (oddRecurrence_implies_adjacent (H M hTotal))
  refine
    { witness := pick
      invariant := ?_ }
  intro M hTotal
  have hSpec :=
    Classical.choose_spec
      (oddRecurrence_implies_adjacent (H M hTotal))
  simpa [pick, ObsEquiv] using hSpec

theorem totalOddRecurrence_implies_universalFailure
    (H : TotalOddSemanticRecurrence) :
    UniversalFailure CanonicalSAT :=
  invariantProducer_implies_universalFailure
    (oddRecurrence_to_invariantProducer H)

theorem totalOddRecurrence_closes_internal_endpoint
    (H : TotalOddSemanticRecurrence) :
    PneqNP :=
  invariantProducer_closes_internal_endpoint
    (oddRecurrence_to_invariantProducer H)

/--
Abstract FlipState cannot satisfy odd semantic recurrence: every step negates
the observation, so odd-separated states are observationally opposite.
-/
def FlipOrbit (s0 : FlipState) : Nat → FlipState
  | 0 => s0
  | n + 1 => flipStep (FlipOrbit s0 n)

theorem flipOrbit_accept_flip
    (s0 : FlipState)
    (k : Nat) :
    flipAccept (FlipOrbit s0 (k + 1)) ↔
      ¬ flipAccept (FlipOrbit s0 k) := by
  simpa [FlipOrbit] using flipStep_negates_accept (FlipOrbit s0 k)

theorem flipOrbit_odd_not_equiv
    (s0 : FlipState)
    (i d : Nat) :
    ¬ (flipAccept (FlipOrbit s0 i) ↔
        flipAccept (FlipOrbit s0 (i + (2 * d + 1)))) := by
  have hNeg :
      flipAccept (FlipOrbit s0 (i + (2 * d + 1))) ↔
        ¬ flipAccept (FlipOrbit s0 i) :=
    odd_flips_negate
      (P := fun k => flipAccept (FlipOrbit s0 k))
      (flipOrbit_accept_flip s0) i d
  by_cases hAi : flipAccept (FlipOrbit s0 i)
  · intro hEq
    have hAj := hEq.mp hAi
    exact (hNeg.mp hAj) hAi
  · intro hEq
    have hAj := hNeg.mpr hAi
    exact hAi (hEq.mpr hAj)

#print axioms MCore.Real.P02OddSemanticRecurrence.oddGap_lt
#print axioms MCore.Real.P02OddSemanticRecurrence.oddGap_ne
#print axioms MCore.Real.P02OddSemanticRecurrence.two_flips_restore
#print axioms MCore.Real.P02OddSemanticRecurrence.odd_flips_negate
#print axioms MCore.Real.P02OddSemanticRecurrence.no_adjacent_equiv_implies_flip
#print axioms MCore.Real.P02OddSemanticRecurrence.oddRecurrence_implies_adjacent
#print axioms MCore.Real.P02OddSemanticRecurrence.oddRecurrence_to_invariantProducer
#print axioms MCore.Real.P02OddSemanticRecurrence.totalOddRecurrence_implies_universalFailure
#print axioms MCore.Real.P02OddSemanticRecurrence.totalOddRecurrence_closes_internal_endpoint
#print axioms MCore.Real.P02OddSemanticRecurrence.flipOrbit_odd_not_equiv

end P02OddSemanticRecurrence
end Real
end MCore
