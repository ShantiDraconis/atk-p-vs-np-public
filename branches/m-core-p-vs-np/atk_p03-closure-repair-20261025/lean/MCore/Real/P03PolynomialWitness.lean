import MCore.Real.P03TerminalSemanticBridge
import Mathlib

namespace MCore
namespace Real
namespace P03PolynomialWitness

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TableauDynamics
open P03TerminalSemanticBridge

/-- Affine odd-gap polynomial: j = P1(i,d). -/
def P1 (i d : ℝ) : ℝ :=
  i + 2 * d + 1

/-- Vanishing form of the odd-gap polynomial. -/
def P2 (i j d : ℝ) : ℝ :=
  j - i - 2 * d - 1

/-- Unit-gap polynomial.  Its real zero set is j-i = ±1. -/
def P3 (i j : ℝ) : ℝ :=
  (j - i)^2 - 1

theorem p1_p2_exact
    (i j d : ℝ) :
    P2 i j d = 0 ↔ j = P1 i d := by
  unfold P1 P2
  constructor <;> intro h <;> linarith

theorem p3_zero_iff_unit_gap
    (i j : ℝ) :
    P3 i j = 0 ↔ j - i = 1 ∨ j - i = -1 := by
  unfold P3
  constructor
  · intro h
    have hfac : (j - i - 1) * (j - i + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with h₁ | h₂
    · left
      nlinarith
    · right
      nlinarith
  · rintro (h | h) <;> nlinarith

/--
Polynomial energy attached to an actual polynomial Q.
Zero energy means simultaneously:
  * the odd-gap affine equation vanishes;
  * Q takes the same value at i and j.
-/
def WitnessEnergy
    (Q : Polynomial ℝ)
    (i j d : ℝ) : ℝ :=
  (P2 i j d)^2 + (Q.eval i - Q.eval j)^2

theorem witnessEnergy_nonneg
    (Q : Polynomial ℝ)
    (i j d : ℝ) :
    0 ≤ WitnessEnergy Q i j d := by
  unfold WitnessEnergy
  positivity

/-- Exact sum-of-squares certificate; no critical-point surrogate is used. -/
theorem witnessEnergy_eq_zero_iff
    (Q : Polynomial ℝ)
    (i j d : ℝ) :
    WitnessEnergy Q i j d = 0 ↔
      P2 i j d = 0 ∧ Q.eval i = Q.eval j := by
  unfold WitnessEnergy
  constructor
  · intro h
    have hp2 : P2 i j d = 0 := by
      nlinarith [sq_nonneg (P2 i j d), sq_nonneg (Q.eval i - Q.eval j)]
    have hq : Q.eval i - Q.eval j = 0 := by
      nlinarith [sq_nonneg (P2 i j d), sq_nonneg (Q.eval i - Q.eval j)]
    exact ⟨hp2, by linarith⟩
  · rintro ⟨hp2, hq⟩
    simp [WitnessEnergy, hp2, hq]

/-- The affine gap polynomial has no zero-gradient issue: its coefficients are fixed. -/
theorem p2_coefficients_nonzero :
    ((-1 : ℝ), (1 : ℝ), (-2 : ℝ)) ≠ (0, 0, 0) := by
  norm_num

/--
A concrete warning against replacing S=0 by ∇S=0.
The polynomial q(x)=x^3/3-x^2/2 has q'(0)=q'(1)=0 but q(0)≠q(1).
Thus stationary points alone cannot certify acceptance equality.
-/
def CriticalCounterexampleQ (x : ℝ) : ℝ :=
  x^3 / 3 - x^2 / 2

def CriticalCounterexampleQDeriv (x : ℝ) : ℝ :=
  x^2 - x

theorem critical_counterexample_stationary :
    CriticalCounterexampleQDeriv 0 = 0 ∧
    CriticalCounterexampleQDeriv 1 = 0 := by
  norm_num [CriticalCounterexampleQDeriv]

theorem critical_counterexample_values_differ :
    CriticalCounterexampleQ 0 ≠ CriticalCounterexampleQ 1 := by
  norm_num [CriticalCounterexampleQ]

/-- Boolean acceptance embedded faithfully into the reals. -/
def BoolValue (b : Bool) : ℝ :=
  if b then 1 else 0

theorem boolValue_injective :
    Function.Injective BoolValue := by
  intro a b h
  cases a <;> cases b <;> simp [BoolValue] at h ⊢

/-- Actual complete-run acceptance bit at the k-th outer orbit input. -/
def OrbitAcceptance
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (k : Nat) : Bool :=
  M.accepting
    (FinalRunState M
      (Orbit (R_M M hTotal) seed k))

/--
Exact local polynomial sampling certificate for one proposed natural witness.
The polynomial is not assumed to encode the whole infinite orbit; it is only
required to agree with the actual acceptance observable at the two sampled
indices.  Hence this structure cannot hide an infinite interpolation
assumption.
-/
structure PolynomialWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i : Nat
  j : Nat
  d : Nat
  odd : j = i + (2 * d + 1)
  Q : Polynomial ℝ
  sample_i :
    Q.eval (i : ℝ) = BoolValue (OrbitAcceptance M hTotal seed i)
  sample_j :
    Q.eval (j : ℝ) = BoolValue (OrbitAcceptance M hTotal seed j)
  energy_zero :
    WitnessEnergy Q (i : ℝ) (j : ℝ) (d : ℝ) = 0

/-- A polynomial witness yields the actual terminal full-run witness. -/
def PolynomialWitness.toFullRunWitness
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : PolynomialWitness M hTotal) :
    FullRunAcceptanceWitness M hTotal := by
  have henergy :=
    (witnessEnergy_eq_zero_iff W.Q (W.i : ℝ) (W.j : ℝ) (W.d : ℝ)).1
      W.energy_zero
  have hq : W.Q.eval (W.i : ℝ) = W.Q.eval (W.j : ℝ) := henergy.2
  have hbool :
      OrbitAcceptance M hTotal W.seed W.i =
        OrbitAcceptance M hTotal W.seed W.j := by
    apply boolValue_injective
    rw [← W.sample_i, ← W.sample_j]
    exact hq
  refine
    { pair :=
        { seed := W.seed
          i := W.i
          j := W.j
          odd := ?_ }
      acceptance := ?_ }
  · exact ⟨W.d, W.odd⟩
  · simpa [FullRunAcceptEquivalent, OrbitAcceptance,
      FullInputOrbitPair.left, FullInputOrbitPair.right] using hbool

/--
Conversely, every genuine terminal witness has a constant-polynomial energy
certificate.  Therefore polynomialization is an exact reformulation, not a
new assumption and not a proof of existence.
-/
def PolynomialWitness.ofFullRunWitness
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : FullRunAcceptanceWitness M hTotal) :
    PolynomialWitness M hTotal := by
  rcases W.pair.odd with ⟨d, hodd⟩
  let b := OrbitAcceptance M hTotal W.pair.seed W.pair.i
  let Q : Polynomial ℝ := Polynomial.C (BoolValue b)
  have hacc :
      OrbitAcceptance M hTotal W.pair.seed W.pair.i =
        OrbitAcceptance M hTotal W.pair.seed W.pair.j := by
    simpa [FullRunAcceptEquivalent, OrbitAcceptance,
      FullInputOrbitPair.left, FullInputOrbitPair.right] using W.acceptance
  refine
    { seed := W.pair.seed
      i := W.pair.i
      j := W.pair.j
      d := d
      odd := hodd
      Q := Q
      sample_i := ?_
      sample_j := ?_
      energy_zero := ?_ }
  · simp [Q, b]
  · simp [Q, b, hacc]
  · have hp2 :
        P2 (W.pair.i : ℝ) (W.pair.j : ℝ) (d : ℝ) = 0 := by
      unfold P2
      rw [hodd]
      push_cast
      ring
    apply
      (witnessEnergy_eq_zero_iff Q
        (W.pair.i : ℝ) (W.pair.j : ℝ) (d : ℝ)).2
    refine ⟨hp2, ?_⟩
    simp [Q]

theorem polynomialWitness_iff_fullRunWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    Nonempty (PolynomialWitness M hTotal) ↔
      Nonempty (FullRunAcceptanceWitness M hTotal) := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.toFullRunWitness⟩
  · rintro ⟨W⟩
    exact ⟨PolynomialWitness.ofFullRunWitness W⟩

/--
The global polynomial witness law is exactly the existing open terminal law.
No scaffold is gained: proving this law is proving FullRunAcceptanceLaw.
-/
def PolynomialWitnessLaw : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (PolynomialWitness M hTotal)

theorem polynomialWitnessLaw_iff_fullRunAcceptanceLaw :
    PolynomialWitnessLaw ↔ FullRunAcceptanceLaw := by
  constructor
  · intro H M hTotal
    exact (polynomialWitness_iff_fullRunWitness M hTotal).1 (H M hTotal)
  · intro H M hTotal
    exact (polynomialWitness_iff_fullRunWitness M hTotal).2 (H M hTotal)

#print axioms MCore.Real.P03PolynomialWitness.p1_p2_exact
#print axioms MCore.Real.P03PolynomialWitness.p3_zero_iff_unit_gap
#print axioms MCore.Real.P03PolynomialWitness.witnessEnergy_eq_zero_iff
#print axioms MCore.Real.P03PolynomialWitness.critical_counterexample_stationary
#print axioms MCore.Real.P03PolynomialWitness.critical_counterexample_values_differ
#print axioms MCore.Real.P03PolynomialWitness.boolValue_injective
#print axioms MCore.Real.P03PolynomialWitness.polynomialWitness_iff_fullRunWitness
#print axioms MCore.Real.P03PolynomialWitness.polynomialWitnessLaw_iff_fullRunAcceptanceLaw

end P03PolynomialWitness
end Real
end MCore
