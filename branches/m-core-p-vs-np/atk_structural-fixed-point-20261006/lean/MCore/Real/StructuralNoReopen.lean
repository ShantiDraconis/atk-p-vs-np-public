import MCore.Real.StructuralFixedPoint
import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace StructuralNoReopen

-- Frozen no-reopen policy: gain-zero routes are classification-only.

open CanonicalFinalProof
open P02TerminalForcingG2

/--
Zero-gain refinement: the target is logically equivalent to the terminal
proposition. Such a refinement may reorganize parameters but cannot by itself
supply new terminal information.
-/
structure GainZero (P : Prop) where
  Target : Prop
  sound : Target → P
  complete : P → Target

theorem gainZero_fixed_point
    {P : Prop}
    (R : GainZero P) :
    R.Target ↔ P :=
  ⟨R.sound, R.complete⟩

/--
Positive break: explicit new information plus a closing map into P.
This is intentionally one-way. It does not assert that every proof of P must
arise from this structure.
-/
structure PositiveBreak (P : Prop) where
  NewInformation : Prop
  material : NewInformation
  closes : NewInformation → P

theorem close_from_positive_break
    {P : Prop}
    (B : PositiveBreak P) :
    P :=
  B.closes B.material

/--
A zero-gain chain remains equivalent to the original terminal proposition at
every finite stage.
-/
theorem no_reopen_zero_gain_chain
    {P : Prop}
    (E : Nat → Prop)
    (h0 : E 0 ↔ P)
    (step : ∀ n : Nat, E (n + 1) ↔ E n) :
    ∀ n : Nat, E n ↔ P :=
  StructuralFixedPoint.zero_gain_chain
    { stage := E, base := h0, step := step }

/--
Uniformization is explicitly classified as zero-gain.
-/
def uniformizationGainZero
    {A W : Type}
    (R : A → W → Prop) :
    GainZero (∀ a : A, ∃ w : W, R a w) where
  Target := ∃ F : A → W, ∀ a : A, R a (F a)
  sound := fun h =>
    (StructuralFixedPoint.pointwise_iff_uniform_selector).mpr h
  complete := fun h =>
    (StructuralFixedPoint.pointwise_iff_uniform_selector).mp h

/--
Operational De Morgan splitting is explicitly classified as zero-gain.
-/
def deMorganGainZero
    (A B : Prop) :
    GainZero (¬ (A ∧ B)) where
  Target := ¬ A ∨ ¬ B
  sound := (StructuralFixedPoint.neg_and_iff_neg_or_neg).mpr
  complete := (StructuralFixedPoint.neg_and_iff_neg_or_neg).mp

/--
G2 pointwise expansion is a zero-gain refinement of the exposed terminal.
-/
def g2PointwiseGainZero :
    GainZero P02TerminalForcingG2.G2_TERMINAL where
  Target :=
    ∀ M : PolyDTMCandidate,
      ∃ x : BitString,
        ¬ M.CorrectAt P02TerminalForcingG2.CanonicalSAT x
  sound :=
    (StructuralFixedPoint.g2_structural_fixed_point).mp
  complete :=
    (StructuralFixedPoint.g2_structural_fixed_point).mpr

/--
No-reopen theorem for the currently formalized G2 pointwise route.
It proves only equivalence, not G2 itself.
-/
theorem g2_no_reopen :
    g2PointwiseGainZero.Target ↔
      P02TerminalForcingG2.G2_TERMINAL :=
  gainZero_fixed_point g2PointwiseGainZero

/--
A genuinely material theorem that closes G2 can be packaged as a positive
break without introducing a reverse equivalence.
-/
def g2PositiveBreakOf
    (H : Prop)
    (hH : H)
    (close : H → P02TerminalForcingG2.G2_TERMINAL) :
    PositiveBreak P02TerminalForcingG2.G2_TERMINAL where
  NewInformation := H
  material := hH
  closes := close

theorem g2_close_from_positive_break
    (B : PositiveBreak P02TerminalForcingG2.G2_TERMINAL) :
    P02TerminalForcingG2.G2_TERMINAL :=
  close_from_positive_break B

inductive FinalizationState where
  | truncatedReal
  | exposedGreen
  | closedGreen
  deriving DecidableEq, Repr

/--
Repository policy as data: zero-gain structural refinements terminate in the
truncated/exposed states; CLOSED_GREEN requires a material positive break.
-/
structure FinalizationRecord (P : Prop) where
  state : FinalizationState
  endpoint : Prop
  endpoint_eq : endpoint ↔ P
  materialProof : Option (PLift P)

def g2ExposedRecord :
    FinalizationRecord P02TerminalForcingG2.G2_TERMINAL where
  state := .exposedGreen
  endpoint := P02TerminalForcingG2.G2_TERMINAL
  endpoint_eq := Iff.rfl
  materialProof := none

#print axioms MCore.Real.StructuralNoReopen.gainZero_fixed_point
#print axioms MCore.Real.StructuralNoReopen.close_from_positive_break
#print axioms MCore.Real.StructuralNoReopen.no_reopen_zero_gain_chain
#print axioms MCore.Real.StructuralNoReopen.g2_no_reopen
#print axioms MCore.Real.StructuralNoReopen.g2_close_from_positive_break
#print axioms MCore.Real.StructuralNoReopen.g2ExposedRecord

end StructuralNoReopen
end Real
end MCore
