import MCore.Real.P02UniversalFailureWitnessMaterial

namespace MCore
namespace Real
namespace StructuralDiagonalObstruction

open CanonicalFinalProof

/--
Finite self-embedding obstruction.

Any code transformer that strictly increases bitstring length has no literal
fixed point. Therefore a material semantic diagonal cannot be justified merely
by claiming that a finite code literally contains a strictly larger copy of
itself.
-/
theorem strict_length_no_literal_fixed_point
    (D : BitString → BitString)
    (hGrow : ∀ x : BitString, x.length < (D x).length) :
    ∀ x : BitString, D x ≠ x := by
  intro x hEq
  have h := hGrow x
  rw [hEq] at h
  exact (Nat.lt_irrefl x.length) h

/-- Explicit finite iteration, used to expose expansion loops. -/
def iterateCode
    (D : BitString → BitString) :
    Nat → BitString → BitString
  | 0, x => x
  | n + 1, x => D (iterateCode D n x)

/--
Strict expansion remains strict after every positive finite number of
iterations.
-/
theorem iterateCode_length_strict
    (D : BitString → BitString)
    (hGrow : ∀ x : BitString, x.length < (D x).length) :
    ∀ (n : Nat) (x : BitString),
      x.length < (iterateCode D (n + 1) x).length := by
  intro n
  induction n with
  | zero =>
      intro x
      exact hGrow x
  | succ n ih =>
      intro x
      have h1 : x.length < (iterateCode D (n + 1) x).length :=
        ih x
      have h2 :
          (iterateCode D (n + 1) x).length <
            (D (iterateCode D (n + 1) x)).length :=
        hGrow (iterateCode D (n + 1) x)
      exact Nat.lt_trans h1 h2

/--
A strictly expanding finite-code operator has no positive-period finite cycle.
This rules out not only x = D x but also attempts to obtain a literal fixed
point by repeatedly opening code/serialization layers and returning after a
finite number of steps.
-/
theorem strict_length_no_positive_cycle
    (D : BitString → BitString)
    (hGrow : ∀ x : BitString, x.length < (D x).length) :
    ∀ (n : Nat) (x : BitString),
      iterateCode D (n + 1) x ≠ x := by
  intro n x hEq
  have h := iterateCode_length_strict D hGrow n x
  rw [hEq] at h
  exact (Nat.lt_irrefl x.length) h

/--
Consequently, any successful diagonal input in the canonical finite-bitstring
model must use semantic self-reference rather than a literal fixed point of a
strictly expanding serialization operator.
-/
def SemanticDiagonalRequirement
    (diagonalInput : PolyDTMCandidate → BitString) : Prop :=
  ∀ M : PolyDTMCandidate,
    P02UniversalFailureWitnessMaterial.CanonicalSAT (diagonalInput M) ↔
      ¬ (
        M.accepting
          (M.machine.run
            (M.timeBound (diagonalInput M).length)
            (initialTMConfig M.machine (diagonalInput M))).state = true
      )

#print axioms MCore.Real.StructuralDiagonalObstruction.strict_length_no_literal_fixed_point
#print axioms MCore.Real.StructuralDiagonalObstruction.iterateCode_length_strict
#print axioms MCore.Real.StructuralDiagonalObstruction.strict_length_no_positive_cycle

end StructuralDiagonalObstruction
end Real
end MCore
