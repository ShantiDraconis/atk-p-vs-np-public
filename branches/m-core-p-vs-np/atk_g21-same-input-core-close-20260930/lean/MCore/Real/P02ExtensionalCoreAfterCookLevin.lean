import MCore.Real.P02ExtensionalSameInputBridge
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose

namespace MCore
namespace Real
namespace P02ExtensionalCoreAfterCookLevin

open CanonicalFinalProof
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02G21G22Attack
open P02ExtensionalSameInputBridge
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose

/-- Minimal live extensional core after bounded Cook-Levin correctness has
already been kernelized.

No SAT-correctness field remains here.  The only nontrivial obligation is to
build a computable code transformer whose semantics-invariant input carrier is
realized syntactically by the canonical reject circuit. -/
structure ExtensionalRejectCompilerCore
    (M : PolyDTMCandidate) where
  compile : Nat.Partrec.Code → Nat.Partrec.Code
  compile_computable : Computable compile
  selfInput : Nat.Partrec.Code → BitString
  selfInput_ext :
    ∀ a b : Nat.Partrec.Code,
      Nat.Partrec.Code.eval a = Nat.Partrec.Code.eval b →
      selfInput a = selfInput b
  compile_realizes :
    ∀ c : Nat.Partrec.Code,
      selfInput (compile c) =
        encodeCircuit (rejectCircuit M (selfInput c))

/-- Cook-Levin correctness is derived, not assumed. -/
def ExtensionalRejectCompilerCore.toCompiler
    {M : PolyDTMCandidate}
    (E : ExtensionalRejectCompilerCore M) :
    ExtensionalSameInputCompiler M where
  compile := E.compile
  compile_computable := E.compile_computable
  circuitOf := fun c => rejectCircuit M (E.selfInput c)
  selfInput := E.selfInput
  selfInput_ext := E.selfInput_ext
  compile_realizes := E.compile_realizes
  cook_levin_correct := by
    intro c
    exact rejectCircuit_cook_levin_correct
      boundedExecCorrectness_closed M (E.selfInput c)

structure UniformExtensionalRejectCompilerCore where
  core :
    ∀ M : PolyDTMCandidate,
      ExtensionalRejectCompilerCore M

def UniformExtensionalRejectCompilerCore.toUniformCompiler
    (U : UniformExtensionalRejectCompilerCore) :
    UniformExtensionalSameInputCompiler where
  compiler := fun M => (U.core M).toCompiler

theorem uniform_core_closes_G21
    (U : UniformExtensionalRejectCompilerCore) :
    G21Pointwise :=
  uniform_extensional_bridge_closes_G21 U.toUniformCompiler

theorem uniform_core_closes_P02
    (U : UniformExtensionalRejectCompilerCore) :
    P02TerminalFrontier.P02Target :=
  uniform_extensional_bridge_closes_P02 U.toUniformCompiler

/-- Exact remaining extensional construction target after Cook-Levin closure. -/
def UniformExtensionalRejectCompilerCoreGap : Prop :=
  Nonempty UniformExtensionalRejectCompilerCore

theorem core_gap_closes_G21
    (h : UniformExtensionalRejectCompilerCoreGap) :
    G21Pointwise := by
  rcases h with ⟨U⟩
  exact uniform_core_closes_G21 U

#print axioms MCore.Real.P02ExtensionalCoreAfterCookLevin.ExtensionalRejectCompilerCore.toCompiler
#print axioms MCore.Real.P02ExtensionalCoreAfterCookLevin.uniform_core_closes_G21
#print axioms MCore.Real.P02ExtensionalCoreAfterCookLevin.core_gap_closes_G21

end P02ExtensionalCoreAfterCookLevin
end Real
end MCore
