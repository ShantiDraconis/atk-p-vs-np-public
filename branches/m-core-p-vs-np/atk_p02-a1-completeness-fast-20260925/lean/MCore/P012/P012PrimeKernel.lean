import MCore.P012.P012PrimeTransitionBoundary

namespace MCore
namespace P012

structure PrimeKernel where
  q : Nat
  hq : 0 < q

def kernelNumerator : Int := 2

def kernelState (_K : PrimeKernel) : ThirdState := ⟨kernelNumerator⟩
def kernelMirrorState (_K : PrimeKernel) : ThirdState := ⟨-kernelNumerator⟩

theorem two_is_prime : PrimeNat 2 := primeNat_two

theorem two_is_least_prime
    {p : Nat} (hp : PrimeNat p) :
    2 ≤ p :=
  hp.1

def reflectNumerator (z : Int) : Int := -z

def reflectState (s : ThirdState) : ThirdState :=
  ⟨reflectNumerator s.numerator⟩

theorem reflect_involutive (s : ThirdState) :
    reflectState (reflectState s) = s := by
  cases s
  simp [reflectState, reflectNumerator]

theorem kernel_reflection :
    reflectState ⟨-2⟩ = ⟨2⟩ := by
  decide

def kernelDistance (s : ThirdState) : Nat :=
  Int.natAbs s.numerator - 2

def CompressesTowardKernel (a b : ThirdState) : Prop :=
  2 ≤ Int.natAbs b.numerator ∧
  Int.natAbs b.numerator ≤ Int.natAbs a.numerator

def ExpandsFromKernel (a b : ThirdState) : Prop :=
  2 ≤ Int.natAbs a.numerator ∧
  Int.natAbs a.numerator ≤ Int.natAbs b.numerator

theorem compress_neg7_to_neg2 :
    CompressesTowardKernel ⟨-7⟩ ⟨-2⟩ := by
  constructor <;> decide

theorem expand_2_to_7 :
    ExpandsFromKernel ⟨2⟩ ⟨7⟩ := by
  constructor <;> decide

theorem kernel_reflection_displacement :
    displacementNumerator ⟨-2⟩ ⟨2⟩ = 4 := by decide

theorem kernel_is_not_zero_numerator :
    kernelNumerator ≠ 0 := by decide

theorem kernel_is_not_one_numerator :
    kernelNumerator ≠ 1 := by decide

#print axioms MCore.P012.two_is_least_prime
#print axioms MCore.P012.kernel_reflection
#print axioms MCore.P012.compress_neg7_to_neg2
#print axioms MCore.P012.expand_2_to_7

end P012
end MCore
