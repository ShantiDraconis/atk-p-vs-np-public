import MCore.Real.P02FiniteDescriptorResidualCore

namespace MCore
namespace Real
namespace P02FiniteDescriptorStructuralLaws

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FiniteDescriptorReduction
open P02FiniteDescriptorResidualCore
open P02SemanticTransformerDichotomy
open P02SemanticTransformerCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def finalState
    (D : FiniteDTMDescriptor)
    (x : BitString) :
    Fin (D.stateCount + 1) :=
  (D.toCandidate.machine.run
    (D.toCandidate.timeBound x.length)
    (initialTMConfig D.toCandidate.machine x)).state

theorem false_final_rejects
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    D.accepting (finalState D falseBits) = false := by
  have hNot : ¬ DeclaredAccept D.toCandidate falseBits :=
    hPattern.1
  unfold DeclaredAccept at hNot
  change D.accepting (finalState D falseBits) ≠ true at hNot
  cases h :
      D.accepting (finalState D falseBits) with
  | false => rfl
  | true => exact False.elim (hNot h)

theorem true_final_accepts
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    D.accepting (finalState D trueBits) = true := by
  have hAcc : DeclaredAccept D.toCandidate trueBits :=
    hPattern.2
  unfold DeclaredAccept at hAcc
  exact hAcc

theorem constant_final_states_distinct
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    finalState D falseBits ≠ finalState D trueBits := by
  intro hEq
  have hFalse := false_final_rejects D hPattern
  have hTrue := true_final_accepts D hPattern
  rw [hEq] at hFalse
  rw [hTrue] at hFalse
  contradiction

/-- Any descriptor surviving the two canonical constants has at least two
physical control states, hence stateCount is strictly positive. -/
theorem stateCount_pos
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    0 < D.stateCount := by
  cases hsc : D.stateCount with
  | zero =>
      have hEq :
          finalState D falseBits = finalState D trueBits := by
        apply Fin.ext
        have hFalse : (finalState D falseBits).val < 1 := by
          simpa [hsc] using (finalState D falseBits).isLt
        have hTrue : (finalState D trueBits).val < 1 := by
          simpa [hsc] using (finalState D trueBits).isLt
        omega
      exact False.elim (constant_final_states_distinct D hPattern hEq)
  | succ n =>
      simp

theorem accepting_nonconstant
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    ∃ qReject qAccept : Fin (D.stateCount + 1),
      qReject ≠ qAccept ∧
      D.accepting qReject = false ∧
      D.accepting qAccept = true := by
  refine ⟨finalState D falseBits, finalState D trueBits,
    constant_final_states_distinct D hPattern,
    false_final_rejects D hPattern,
    true_final_accepts D hPattern⟩

/-- A zero monomial coefficient gives zero fuel on every input, so the final
state is the common initial state. Such a descriptor cannot be correct on both
canonical constants. -/
theorem coefficient_pos
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    0 < D.coefficient := by
  cases hc : D.coefficient with
  | zero =>
      have hFalseState :
          finalState D falseBits = D.machine.initial := by
        simp [finalState, FiniteDTMDescriptor.toCandidate,
          monomialTimeBound, hc, TM.run, initialTMConfig]
      have hTrueState :
          finalState D trueBits = D.machine.initial := by
        simp [finalState, FiniteDTMDescriptor.toCandidate,
          monomialTimeBound, hc, TM.run, initialTMConfig]
      have hDistinct := constant_final_states_distinct D hPattern
      exact False.elim (hDistinct (by rw [hFalseState, hTrueState]))
  | succ n =>
      simp

structure ResidualStructuralCertificate
    (D : FiniteDTMDescriptor) : Prop where
  stateCount_pos : 0 < D.stateCount
  coefficient_pos : 0 < D.coefficient
  accepting_nonconstant :
    ∃ qReject qAccept : Fin (D.stateCount + 1),
      qReject ≠ qAccept ∧
      D.accepting qReject = false ∧
      D.accepting qAccept = true

theorem structural_certificate_of_constant_correct
    (D : FiniteDTMDescriptor)
    (hPattern : DescriptorConstantCorrect D) :
    ResidualStructuralCertificate D :=
  ⟨stateCount_pos D hPattern,
   coefficient_pos D hPattern,
   accepting_nonconstant D hPattern⟩

/-- Equivalent residual with the forced structural laws made explicit. -/
def FiniteDescriptorStructuralResidual : Prop :=
  ∀ D : FiniteDTMDescriptor,
    DescriptorTotal D →
    DescriptorConstantCorrect D →
    ResidualStructuralCertificate D →
      ∃ x : BitString,
        P02FailureNormalForms.SemanticDisagreement D.toCandidate x

theorem structuralResidual_iff_residual :
    FiniteDescriptorStructuralResidual ↔
      FiniteDescriptorResidual := by
  constructor
  · intro H D hTotal hPattern
    exact H D hTotal hPattern
      (structural_certificate_of_constant_correct D hPattern)
  · intro H D hTotal hPattern _
    exact H D hTotal hPattern

theorem structuralResidual_iff_universalFailure :
    FiniteDescriptorStructuralResidual ↔
      UniversalFailure SATTarget := by
  exact structuralResidual_iff_residual.trans
    residual_iff_universalFailure

#print axioms MCore.Real.P02FiniteDescriptorStructuralLaws.constant_final_states_distinct
#print axioms MCore.Real.P02FiniteDescriptorStructuralLaws.stateCount_pos
#print axioms MCore.Real.P02FiniteDescriptorStructuralLaws.coefficient_pos
#print axioms MCore.Real.P02FiniteDescriptorStructuralLaws.accepting_nonconstant
#print axioms MCore.Real.P02FiniteDescriptorStructuralLaws.structuralResidual_iff_universalFailure

end P02FiniteDescriptorStructuralLaws
end Real
end MCore
