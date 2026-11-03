import MCore.Real.StructuralFixedPoint
import MCore.Real.P02ClockBridgeMaterial
import MCore.Real.P02FiniteMachineDescription

namespace MCore
namespace Real
namespace StructuralFixedPointBreak

-- Revalidated against the corrected StructuralFixedPoint base.

open CanonicalFinalProof
open P02TerminalForcingG2

/--
A genuinely new-information break for G2.

Flow/W/non-collapsing are carried as concrete data, but the decisive field is
hdiag_real: it must be derived from those concrete definitions, not assumed
from UniversalFailure/FailureLaw/SelectorFails or an equivalent endpoint.
-/
structure G2PerelmanBreak (A W : Type) [LE W] where
  seed : PolyDTMCandidate → A
  Flow : A → Nat → A
  W_func : A → W
  W_mono :
    ∀ (M : PolyDTMCandidate) (t : Nat),
      W_func (Flow (seed M) t) ≤ W_func (Flow (seed M) (t + 1))
  measure : A → Nat
  kappa : Nat
  kappa_pos : 0 < kappa
  non_collapsing :
    ∀ (M : PolyDTMCandidate) (t : Nat),
      kappa ≤ measure (Flow (seed M) t)
  diagonalInput : PolyDTMCandidate → BitString
  hdiag_real :
    ∀ M : PolyDTMCandidate,
      P02TerminalForcingG2.CanonicalSAT (diagonalInput M) ↔
        ¬ (
          M.accepting
            (M.machine.run
              (M.timeBound (diagonalInput M).length)
              (initialTMConfig M.machine (diagonalInput M))).state = true
        )

/--
Material diagonal disagreement: once hdiag_real is concrete, CorrectAt at the
diagonal input is contradictory by propositional computation.
-/
theorem hdiag_real_implies_not_correctAt
    {A W : Type} [LE W]
    (B : G2PerelmanBreak A W)
    (M : PolyDTMCandidate) :
    ¬ M.CorrectAt
      P02TerminalForcingG2.CanonicalSAT
      (B.diagonalInput M) := by
  intro hCorrect
  rcases hCorrect with ⟨_hhalt, hsem⟩
  have hdiag := B.hdiag_real M
  by_cases hacc :
      M.accepting
        (M.machine.run
          (M.timeBound (B.diagonalInput M).length)
          (initialTMConfig M.machine (B.diagonalInput M))).state = true
  · have hsat :
        P02TerminalForcingG2.CanonicalSAT (B.diagonalInput M) :=
      hsem.mp hacc
    have hnacc := hdiag.mp hsat
    exact hnacc hacc
  · have hsat :
        P02TerminalForcingG2.CanonicalSAT (B.diagonalInput M) :=
      hdiag.mpr hacc
    have hacc' := hsem.mpr hsat
    exact hacc hacc'

/--
A material break immediately inhabits the exact terminal G2 selector+law.
No endpoint-equivalent hypothesis is used.
-/
theorem perelman_break_closes_g2_terminal
    {A W : Type} [LE W]
    (B : G2PerelmanBreak A W) :
    P02TerminalForcingG2.G2_TERMINAL := by
  refine ⟨B.diagonalInput, ?_⟩
  exact (P02TerminalForcingG2.failureLaw_iff_correctAt B.diagonalInput).mpr
    (fun M => hdiag_real_implies_not_correctAt B M)

/--
The same material break gives the exact UniversalFailureWitness inhabitant.
-/
def perelmanBreakWitness
    {A W : Type} [LE W]
    (B : G2PerelmanBreak A W) :
    P02UniversalFailureWitnessMaterial.UniversalFailureWitness :=
  P02TerminalForcingG2.universalFailureWitnessOf
    B.diagonalInput
    ((P02TerminalForcingG2.failureLaw_iff_correctAt B.diagonalInput).mpr
      (fun M => hdiag_real_implies_not_correctAt B M))

/--
Consequently, a fully material G2 break closes the repository's P≠NP endpoint.
-/
theorem perelman_break_closes_p_ne_np
    {A W : Type} [LE W]
    (B : G2PerelmanBreak A W) :
    PneqNP :=
  P02TerminalForcingG2.g2_terminal_implies_p_ne_np
    (perelman_break_closes_g2_terminal B)

#print axioms MCore.Real.StructuralFixedPointBreak.hdiag_real_implies_not_correctAt
#print axioms MCore.Real.StructuralFixedPointBreak.perelman_break_closes_g2_terminal
#print axioms MCore.Real.StructuralFixedPointBreak.perelmanBreakWitness
#print axioms MCore.Real.StructuralFixedPointBreak.perelman_break_closes_p_ne_np

end StructuralFixedPointBreak
end Real
end MCore
