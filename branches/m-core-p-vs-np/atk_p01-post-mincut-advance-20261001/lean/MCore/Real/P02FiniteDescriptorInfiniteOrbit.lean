import MCore.Real.P02OpenMathRouteFalsification
import MCore.Real.P02FiniteDescriptorAlternation

namespace MCore
namespace Real
namespace P02FiniteDescriptorInfiniteOrbit

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02OpenMathRouteFalsification
open P02ComplementTableauDiagonal
open P02DiagonalOrbitCore
open P02FiniteDescriptorReduction
open P02FiniteDescriptorOrbitResidual
open P02FiniteDescriptorAlternation
open P02SemanticTransformerDichotomy

/-- The canonical complement-tableau diagonal transform strictly increases
bitstring length. This is a structural theorem about the concrete encoding. -/
theorem diagonalBits_strict_growth
    (M : PolyDTMCandidate)
    (x : BitString) :
    x.length < (diagonalBits M x).length := by
  let t := M.timeBound x.length
  have hcnf :
      x.length <
        (boundedExecTableauCNF
          (P02ComplementTableauDiagonal.complementCandidate M) x t).length :=
    boundedExecTableauCNF_length_gt_input
      (P02ComplementTableauDiagonal.complementCandidate M) x t
  have henc :
      (boundedExecTableauCNF
        (P02ComplementTableauDiagonal.complementCandidate M) x t).length ≤
      (encodeCircuit
        (cnfCircuit
          (boundedExecTableauCNF
            (P02ComplementTableauDiagonal.complementCandidate M) x t))).length :=
    cnfCircuit_encode_length_ge_clause_count _
  unfold diagonalBits boundedExecBits boundedExecCircuit
  exact Nat.lt_of_lt_of_le hcnf henc

theorem orbit_length_step
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    (orbit M seed n).length <
      (orbit M seed (n + 1)).length := by
  simpa [orbit] using
    diagonalBits_strict_growth M (orbit M seed n)

/-- Monotonicity of orbit length, proved only from the concrete one-step
growth law. -/
theorem orbit_length_le_of_le
    (M : PolyDTMCandidate)
    (seed : BitString)
    {i j : Nat}
    (hij : i ≤ j) :
    (orbit M seed i).length ≤ (orbit M seed j).length := by
  induction hij with
  | refl =>
      exact Nat.le_refl _
  | @step j hij ih =>
      exact Nat.le_trans ih
        (Nat.le_of_lt (orbit_length_step M seed j))

theorem orbit_length_lt_of_lt
    (M : PolyDTMCandidate)
    (seed : BitString)
    {i j : Nat}
    (hij : i < j) :
    (orbit M seed i).length < (orbit M seed j).length := by
  have hsucc : i + 1 ≤ j := hij
  exact Nat.lt_of_lt_of_le
    (orbit_length_step M seed i)
    (orbit_length_le_of_le M seed hsucc)

/-- No two different orbit indices can carry the same bitstring. -/
theorem orbit_index_eq_of_bitstring_eq
    (M : PolyDTMCandidate)
    (seed : BitString)
    {i j : Nat}
    (hEq : orbit M seed i = orbit M seed j) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · have hcases : i < j ∨ j < i := Nat.lt_or_gt_of_ne hij
    rcases hcases with hlt | hgt
    · have hlen := congrArg List.length hEq
      have hgrow := orbit_length_lt_of_lt M seed hlt
      exact False.elim ((Nat.ne_of_lt hgrow) hlen)
    · have hlen := congrArg List.length hEq
      have hgrow := orbit_length_lt_of_lt M seed hgt
      exact False.elim ((Nat.ne_of_lt hgrow) hlen.symm)

theorem orbit_ne_next
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    orbit M seed n ≠ orbit M seed (n + 1) := by
  intro h
  have hlen := congrArg List.length h
  exact (Nat.ne_of_lt (orbit_length_step M seed n)) hlen

/-- Local, dependency-free notion of an injective orbit. -/
def OrbitIndexInjective
    (M : PolyDTMCandidate)
    (seed : BitString) : Prop :=
  ∀ i j : Nat,
    orbit M seed i = orbit M seed j → i = j

theorem orbit_index_injective
    (M : PolyDTMCandidate)
    (seed : BitString) :
    OrbitIndexInjective M seed := by
  intro i j h
  exact orbit_index_eq_of_bitstring_eq M seed h

theorem orbit_succ_valid
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    ∃ phi : Circuit,
      decodeCircuit (orbit M seed (n + 1)) = some phi := by
  simpa [orbit] using
    diagonalBits_valid M (orbit M seed n)

/-- Every step contributes at least one additional bit of encoding length. -/
theorem orbit_length_lower_bound
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    seed.length + n ≤ (orbit M seed n).length := by
  induction n with
  | zero =>
      simp [orbit]
  | succ n ih =>
      have hinc :
          seed.length + n + 1 ≤
            (orbit M seed n).length + 1 :=
        Nat.succ_le_succ ih
      have hstep :
          (orbit M seed n).length + 1 ≤
            (orbit M seed (n + 1)).length :=
        Nat.succ_le_of_lt (orbit_length_step M seed n)
      exact Nat.le_trans
        (by simpa [Nat.add_assoc] using hinc)
        hstep

theorem orbit_ne_of_index_ne
    (M : PolyDTMCandidate)
    (seed : BitString)
    {i j : Nat}
    (hij : i ≠ j) :
    orbit M seed i ≠ orbit M seed j := by
  intro h
  exact hij (orbit_index_eq_of_bitstring_eq M seed h)

/-- Unconditional semantic law carried by every diagonal step: the SAT truth
of the next generated instance is exactly the negation of the candidate's
declared answer on the current instance. -/
theorem orbit_next_sat_iff_not_declared_accepts
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    P02UniversalFailureMinCut.CanonicalSAT (orbit M seed (n + 1)) ↔
      ¬ P02SemanticFlipCore.DeclaredAccepts M (orbit M seed n) := by
  simpa [orbit] using
    diagonalBits_sat_iff_not_declaredAccepts
      M (orbit M seed n)

/-- At every concrete diagonal step, either semantic failure is already present
at the next generated SAT instance, or the candidate's declared Boolean answer
must flip relative to the current orbit point. No global lower-bound hypothesis
is used. -/
theorem semantic_disagreement_or_acceptance_flip_step
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    P02FailureNormalForms.SemanticDisagreement
        M (orbit M seed (n + 1)) ∨
      (P02SemanticFlipCore.DeclaredAccepts M (orbit M seed (n + 1)) ↔
        ¬ P02SemanticFlipCore.DeclaredAccepts M (orbit M seed n)) := by
  classical
  by_cases hDis :
      P02FailureNormalForms.SemanticDisagreement
        M (orbit M seed (n + 1))
  · exact Or.inl hDis
  · right
    have hSem :
        P02SemanticFlipCore.DeclaredAccepts M (orbit M seed (n + 1)) ↔
          P02UniversalFailureMinCut.CanonicalSAT (orbit M seed (n + 1)) := by
      apply Classical.byContradiction
      intro hNot
      exact hDis
        ((P02FailureNormalForms.semanticDisagreement_iff_not_semantic_correct
          M (orbit M seed (n + 1))).mpr hNot)
    exact hSem.trans
      (orbit_next_sat_iff_not_declared_accepts M seed n)

/-- Conversely, failure of the forced Boolean flip is already a concrete
semantic counterexample at the next orbit point. -/
theorem semantic_disagreement_of_no_acceptance_flip
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat)
    (hNoFlip :
      ¬ (P02SemanticFlipCore.DeclaredAccepts M (orbit M seed (n + 1)) ↔
          ¬ P02SemanticFlipCore.DeclaredAccepts M (orbit M seed n))) :
    P02FailureNormalForms.SemanticDisagreement
      M (orbit M seed (n + 1)) := by
  rcases semantic_disagreement_or_acceptance_flip_step M seed n with
      hDis | hFlip
  · exact hDis
  · exact False.elim (hNoFlip hFlip)

/-- Surviving residual descriptors therefore carry two infinite, nonrepeating
diagonal orbits, and correctness on them forces exact Boolean alternation. -/
structure InfiniteAlternatingOrbitCertificate
    (D : FiniteDTMDescriptor) : Prop where
  false_injective :
    OrbitIndexInjective D.toCandidate P02SemanticTransformerDichotomy.falseBits
  true_injective :
    OrbitIndexInjective D.toCandidate P02SemanticTransformerDichotomy.trueBits
  false_alternates :
    AlternatingOrbit D.toCandidate P02SemanticTransformerDichotomy.falseBits
  true_alternates :
    AlternatingOrbit D.toCandidate P02SemanticTransformerDichotomy.trueBits

theorem infinite_alternating_certificate
    (D : FiniteDTMDescriptor)
    (hOrbit : DescriptorOrbitCorrect D) :
    InfiniteAlternatingOrbitCertificate D := by
  have hAlt :=
    residual_descriptor_has_two_alternating_orbits D hOrbit
  exact
    { false_injective := orbit_index_injective D.toCandidate P02SemanticTransformerDichotomy.falseBits
      true_injective := orbit_index_injective D.toCandidate P02SemanticTransformerDichotomy.trueBits
      false_alternates := hAlt.1
      true_alternates := hAlt.2 }

#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.diagonalBits_strict_growth
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_length_le_of_le
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_length_lt_of_lt
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_index_eq_of_bitstring_eq
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_succ_valid
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_length_lower_bound
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_ne_of_index_ne
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_next_sat_iff_not_declared_accepts
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.semantic_disagreement_or_acceptance_flip_step
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.semantic_disagreement_of_no_acceptance_flip
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.infinite_alternating_certificate

end P02FiniteDescriptorInfiniteOrbit
end Real
end MCore
