import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega
import MCore.P012.P012OddPrimeGap
import MCore.P012.P012SignedOrientationInterpretation

namespace MCore
namespace P012

/-- General signed displacement numerator for -p/q -> q/q = 1.
The rational displacement is (p+q)/q. -/
def toOneDisplacementNumerator (p q : Nat) : Int :=
  Int.ofNat q - (-(Int.ofNat p))

theorem toOneDisplacementNumerator_eq
    (p q : Nat) :
    toOneDisplacementNumerator p q = Int.ofNat (p + q) := by
  unfold toOneDisplacementNumerator
  omega

/-- Opposite traversal p/q -> -q/q = -1 has displacement -(p+q)/q. -/
def toNegOneDisplacementNumerator (p q : Nat) : Int :=
  -(Int.ofNat q) - Int.ofNat p

theorem toNegOneDisplacementNumerator_eq
    (p q : Nat) :
    toNegOneDisplacementNumerator p q = -(Int.ofNat (p + q)) := by
  unfold toNegOneDisplacementNumerator
  omega

/-- Specialized q=3 facts recover the original 5/3 and -5/3 displacements. -/
theorem negTwoThirds_to_one_numerator :
    toOneDisplacementNumerator 2 3 = 5 := by
  decide

theorem twoThirds_to_negOne_numerator :
    toNegOneDisplacementNumerator 2 3 = -5 := by
  decide

/-- Closed-prime traversal is modeled as compression to the least-prime shell,
reflection across the operational kernel, then expansion. It is not a unit path
through 0 or 1. -/
structure PrimeKernelTraversal where
  start : ThirdState
  leftKernel : ThirdState
  rightKernel : ThirdState
  finish : ThirdState
  compresses : CompressesTowardKernel start leftKernel
  left_is_kernel : leftKernel = ⟨-2⟩
  reflects : reflectState leftKernel = rightKernel
  right_is_kernel : rightKernel = ⟨2⟩
  expands : ExpandsFromKernel rightKernel finish

def demoKernelTraversal : PrimeKernelTraversal where
  start := ⟨-7⟩
  leftKernel := ⟨-2⟩
  rightKernel := ⟨2⟩
  finish := ⟨7⟩
  compresses := compress_neg7_to_neg2
  left_is_kernel := rfl
  reflects := kernel_reflection
  right_is_kernel := rfl
  expands := expand_2_to_7

theorem demoKernelTraversal_closed :
    demoKernelTraversal.leftKernel = ⟨-2⟩ ∧
    demoKernelTraversal.rightKernel = ⟨2⟩ := by
  exact ⟨rfl, rfl⟩

/-- The odd-prime-only model cannot reuse this kernel, because the kernel
numerator 2 is excluded by definition. -/
theorem odd_prime_model_has_no_demo_kernel :
    ¬ OddPrimeThirdState demoKernelTraversal.rightKernel := by
  simpa [demoKernelTraversal] using operational_kernel_not_in_odd_prime_space

/-- Observational P012 reading of the two sides of the kernel traversal. -/
theorem demo_start_is_open_label :
    signedThirdPipelineState demoKernelTraversal.start = .open := by
  simp [demoKernelTraversal, signedThirdPipelineState, orientation,
    orientationToP012, interpretP012]

theorem demo_finish_is_closed_label :
    signedThirdPipelineState demoKernelTraversal.finish = .closed := by
  simp [demoKernelTraversal, signedThirdPipelineState, orientation,
    orientationToP012, interpretP012]

/-
Firewall: PrimeKernelTraversal and its P012 labels are arithmetic/metamodel
objects. No theorem in this file produces P01ConstructionGap, G21Pointwise,
P02Target, OfficialPneqNP, or FinalExternalCertificate.
-/

#print axioms MCore.P012.toOneDisplacementNumerator_eq
#print axioms MCore.P012.demoKernelTraversal_closed
#print axioms MCore.P012.odd_prime_model_has_no_demo_kernel

end P012
end MCore
