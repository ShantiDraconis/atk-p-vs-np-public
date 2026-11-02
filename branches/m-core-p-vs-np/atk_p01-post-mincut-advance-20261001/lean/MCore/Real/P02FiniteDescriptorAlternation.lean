import MCore.Real.P02FiniteDescriptorOrbitResidual

namespace MCore
namespace Real
namespace P02FiniteDescriptorAlternation

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FiniteDescriptorReduction
open P02FiniteDescriptorResidualCore
open P02FiniteDescriptorOrbitResidual
open P02SemanticTransformerDichotomy
open P02ComplementTableauDiagonal
open P02DiagonalOrbitCore
open P02SemanticFlipCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

/-- Correctness at the next diagonal-orbit point forces the candidate's
declared answer to be exactly the complement of its answer at the current
point. -/
theorem orbit_step_acceptance_flips
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat)
    (hNext :
      M.CorrectAt SATTarget (orbit M seed (n + 1))) :
    DeclaredAccepts M (orbit M seed (n + 1)) ↔
      ¬ DeclaredAccepts M (orbit M seed n) := by
  have hSem :
      DeclaredAccepts M (orbit M seed (n + 1)) ↔
        SATTarget (orbit M seed (n + 1)) :=
    hNext.2
  have hDiag :
      SATTarget (orbit M seed (n + 1)) ↔
        ¬ DeclaredAccepts M (orbit M seed n) := by
    simpa [orbit] using
      diagonalBits_sat_iff_not_declaredAccepts
        M (orbit M seed n)
  exact hSem.trans hDiag

/-- An orbit on which the candidate remains correct must alternate forever. -/
def AlternatingOrbit
    (M : PolyDTMCandidate)
    (seed : BitString) : Prop :=
  ∀ n : Nat,
    DeclaredAccepts M (orbit M seed (n + 1)) ↔
      ¬ DeclaredAccepts M (orbit M seed n)

theorem orbitCorrect_implies_alternating
    (M : PolyDTMCandidate)
    (seed : BitString)
    (hOrbit : OrbitCorrect M seed) :
    AlternatingOrbit M seed := by
  intro n
  exact orbit_step_acceptance_flips M seed n (hOrbit (n + 1))

/-- Every descriptor in the final orbit residual class has both canonical
constant-seeded diagonal orbits locked into exact Boolean alternation. -/
theorem residual_descriptor_has_two_alternating_orbits
    (D : FiniteDTMDescriptor)
    (hOrbit : DescriptorOrbitCorrect D) :
    AlternatingOrbit D.toCandidate falseBits ∧
      AlternatingOrbit D.toCandidate trueBits := by
  exact
    ⟨orbitCorrect_implies_alternating
        D.toCandidate falseBits hOrbit.1,
     orbitCorrect_implies_alternating
        D.toCandidate trueBits hOrbit.2⟩

/-- Failure of alternation at any step immediately yields a semantic
counterexample, because correctness at that next orbit point would force the
flip law. -/
theorem failure_of_nonalternating_step
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat)
    (hNoFlip :
      ¬ (DeclaredAccepts M (orbit M seed (n + 1)) ↔
          ¬ DeclaredAccepts M (orbit M seed n))) :
    ¬ M.CorrectAt SATTarget (orbit M seed (n + 1)) := by
  intro hCorrect
  exact hNoFlip
    (orbit_step_acceptance_flips M seed n hCorrect)

#print axioms MCore.Real.P02FiniteDescriptorAlternation.orbit_step_acceptance_flips
#print axioms MCore.Real.P02FiniteDescriptorAlternation.orbitCorrect_implies_alternating
#print axioms MCore.Real.P02FiniteDescriptorAlternation.residual_descriptor_has_two_alternating_orbits
#print axioms MCore.Real.P02FiniteDescriptorAlternation.failure_of_nonalternating_step

end P02FiniteDescriptorAlternation
end Real
end MCore
