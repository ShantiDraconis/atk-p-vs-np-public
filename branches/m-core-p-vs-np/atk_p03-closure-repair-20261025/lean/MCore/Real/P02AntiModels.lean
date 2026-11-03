import MCore.Real.P02OddSemanticRecurrence
import MCore.Real.P02OddParityMixingFrontier

namespace MCore
namespace Real
namespace P02AntiModels

open CanonicalFinalProof
open P02InvariantCore
open P02OddSemanticRecurrence
open P02OddParityMixingFrontier

/-
ANTI-MODEL POLICY

This module records properties that are known to be too weak to close
ODD_PARITY_MIXING_OPEN_MATH.  Nothing here is used as a positive producer.

The purpose is fail-closed:
  * if a proposed Q is satisfied by one of these anti-models, Q is insufficient;
  * if Q kills an anti-model only by assuming literal prefix nesting,
    left-to-right execution, or an unproved surgery-preservation bridge,
    the test is invalid.
-/

/-- Existing minimal anti-model: growth + injectivity + one-step recovery can
coexist with permanent semantic alternation. -/
abbrev WeakFlipState := P02InvariantCore.FlipState
abbrev weakFlipStep := P02InvariantCore.flipStep
abbrev weakFlipAccept := P02InvariantCore.flipAccept
abbrev weakFlipDecode := P02InvariantCore.flipDecode

theorem weakFlip_growth
    (s : WeakFlipState) :
    (weakFlipStep s).depth = s.depth + 1 :=
  P02InvariantCore.flipStep_grows s

theorem weakFlip_injective :
    Function.Injective weakFlipStep :=
  P02InvariantCore.flipStep_injective

theorem weakFlip_recover
    (s : WeakFlipState) :
    weakFlipDecode (weakFlipStep s) = s :=
  P02InvariantCore.flipDecode_step s

theorem weakFlip_permanent_flip
    (s : WeakFlipState) :
    weakFlipAccept (weakFlipStep s) ↔ ¬ weakFlipAccept s :=
  P02InvariantCore.flipStep_negates_accept s

/--
Clock-coupled anti-model.

The boolean observable flips forever while the numerical component obeys the
same second-order clock/radius law used in the exploratory strong-flip test.
This deliberately says nothing about concrete tableau clauses.
-/
structure StrongClockFlipState where
  bit : Bool
  size : Nat
  deriving DecidableEq

def toyClock (n : Nat) : Nat :=
  n ^ 2 + 5

def toyRadius (n : Nat) : Nat :=
  n + toyClock n + 1

def strongClockFlipStep
    (s : StrongClockFlipState) :
    StrongClockFlipState :=
  { bit := !s.bit
    size := toyRadius s.size }

def strongClockFlipAccept
    (s : StrongClockFlipState) : Prop :=
  s.bit = true

@[simp] theorem strongClockFlip_size_law
    (s : StrongClockFlipState) :
    (strongClockFlipStep s).size =
      s.size + toyClock s.size + 1 := by
  rfl

@[simp] theorem strongClockFlip_clock_law
    (s : StrongClockFlipState) :
    toyClock (strongClockFlipStep s).size =
      toyClock (toyRadius s.size) := by
  rfl

theorem strongClockFlip_negates_accept
    (s : StrongClockFlipState) :
    strongClockFlipAccept (strongClockFlipStep s) ↔
      ¬ strongClockFlipAccept s := by
  cases s with
  | mk bit size =>
      cases bit <;>
        simp [strongClockFlipAccept, strongClockFlipStep]

def StrongClockFlipOrbit
    (s0 : StrongClockFlipState) : Nat → StrongClockFlipState
  | 0 => s0
  | n + 1 => strongClockFlipStep (StrongClockFlipOrbit s0 n)

theorem strongClockFlip_orbit_flip
    (s0 : StrongClockFlipState)
    (k : Nat) :
    strongClockFlipAccept (StrongClockFlipOrbit s0 (k + 1)) ↔
      ¬ strongClockFlipAccept (StrongClockFlipOrbit s0 k) := by
  simpa [StrongClockFlipOrbit] using
    strongClockFlip_negates_accept (StrongClockFlipOrbit s0 k)

/--
Exact clock/radius coupling still does not force an odd semantic recurrence:
odd-separated points of this orbit are observationally opposite.
-/
theorem strongClockFlip_odd_not_equiv
    (s0 : StrongClockFlipState)
    (i d : Nat) :
    ¬ (strongClockFlipAccept (StrongClockFlipOrbit s0 i) ↔
       strongClockFlipAccept
         (StrongClockFlipOrbit s0 (i + (2 * d + 1)))) := by
  have hNeg :
      strongClockFlipAccept
          (StrongClockFlipOrbit s0 (i + (2 * d + 1))) ↔
        ¬ strongClockFlipAccept (StrongClockFlipOrbit s0 i) :=
    odd_flips_negate
      (P := fun k =>
        strongClockFlipAccept (StrongClockFlipOrbit s0 k))
      (strongClockFlip_orbit_flip s0) i d
  by_cases hAi : strongClockFlipAccept (StrongClockFlipOrbit s0 i)
  · intro hEq
    have hAj := hEq.mp hAi
    exact (hNeg.mp hAj) hAi
  · intro hEq
    have hAj := hNeg.mpr hAi
    exact hAi (hEq.mpr hAj)

/--
A two-state bipartition can repeat forever while every same-state recurrence
has even distance.  This blocks any argument based on finiteness of the
control-state set alone.
-/
def AlternatingControl : Nat → Bool
  | 0 => false
  | n + 1 => !(AlternatingControl n)

theorem alternatingControl_step
    (n : Nat) :
    AlternatingControl (n + 1) = !(AlternatingControl n) := by
  rfl

theorem alternatingControl_two_step
    (n : Nat) :
    AlternatingControl (n + 2) = AlternatingControl n := by
  cases h : AlternatingControl n <;>
    simp [AlternatingControl, h]

/--
Three repetitions of one finite signature do not force an odd-distance pair.
The concrete revisit set {0,2,4} has three occurrences, but every pairwise
distance is even.  This blocks the proposed "3 visits / 2 parities" argument.
-/
theorem three_revisits_can_all_have_even_gaps :
    let i₁ := 0
    let i₂ := 2
    let i₃ := 4
    i₁ < i₂ ∧ i₂ < i₃ ∧
    ¬ OddGap i₁ i₂ ∧
    ¬ OddGap i₂ i₃ ∧
    ¬ OddGap i₁ i₃ := by
  dsimp
  constructor
  · omega
  constructor
  · omega
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    omega
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    omega
  · intro h
    rcases h with ⟨d, hd⟩
    omega

/--
Control state alone does not inject the input source: every input starts in
the same machine.initial state, while the canonical tape differs with the
input bits.
-/
theorem initial_state_same_for_all_inputs
    (candidate : PolyDTMCandidate)
    (x y : BitString) :
    (initialTMConfig candidate.machine x).state =
      (initialTMConfig candidate.machine y).state := by
  rfl

/--
A concrete witness that equal control state does not imply equal input.
The empty input and [false] have the same initial state but distinct canonical
input tapes.
-/
theorem equal_initial_state_does_not_determine_source
    (candidate : PolyDTMCandidate) :
    (initialTMConfig candidate.machine ([] : BitString)).state =
      (initialTMConfig candidate.machine [false]).state ∧
    ([] : BitString) ≠ [false] := by
  constructor
  · rfl
  · simp

/--
Research guardrail: the current positive frontier is not allowed to rely on
any of the following unproved implications.

  1. R^(k-1)(x) is a literal bit-prefix of R^k(x).
  2. An arbitrary PolyDTMCandidate scans canonical input left-to-right.
  3. Finite |Q|, |Q|+1, or 2|Q|+1 alone forces an odd-gap recurrence.
  4. Clock/radius/encoded-length identities alone imply ObsEquiv.
  5. Adding an odd self-loop to delta_M preserves the original candidate's
     DeclaredAccepts semantics.
  6. Bits encoding a control-state reference force M itself to enter that
     control state while reading those bits.

These are comments by design: turning any of them into an axiom/constant would
invalidate the fail-closed audit.
-/

/--
Positive research target, intentionally not inhabited here.

A future clause-derived phase/mixing law must be strong enough to kill both
WeakFlipState and StrongClockFlipState, while being derived from the concrete
tableau rather than from OddSemanticRecurrence itself.
-/
structure ClauseDerivedMixingLaw
    (M : PolyDTMCandidate)
    (hTotal : P02KleeneUniversalBridge.DeclaredClockTotal M) where
  phase : BitString → Fin 3
  phase_sound :
    ∀ x, True
  /-
  Deliberately no recurrence field: adding OddSemanticRecurrence, ObsEquiv,
  or an equivalent endpoint here would make the structure circular.
  -/

/-- Merely having a three-valued phase classifier carries no closure content. -/
theorem clauseDerivedMixingLaw_is_scaffold_only
    {M : PolyDTMCandidate}
    {hTotal : P02KleeneUniversalBridge.DeclaredClockTotal M}
    (L : ClauseDerivedMixingLaw M hTotal) :
    ∀ x, True :=
  L.phase_sound

#print axioms MCore.Real.P02AntiModels.weakFlip_injective
#print axioms MCore.Real.P02AntiModels.weakFlip_recover
#print axioms MCore.Real.P02AntiModels.strongClockFlip_odd_not_equiv
#print axioms MCore.Real.P02AntiModels.alternatingControl_two_step
#print axioms MCore.Real.P02AntiModels.three_revisits_can_all_have_even_gaps
#print axioms MCore.Real.P02AntiModels.initial_state_same_for_all_inputs
#print axioms MCore.Real.P02AntiModels.equal_initial_state_does_not_determine_source
#print axioms MCore.Real.P02AntiModels.clauseDerivedMixingLaw_is_scaffold_only

end P02AntiModels
end Real
end MCore
