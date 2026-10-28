import Mathlib.Computability.PartrecCode
import MCore.Real.OpenMathCore.SameInputClosure

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier

/-- Forward-only recursion-theoretic producer boundary for one candidate.
    Self-reference is extensional at Code.eval; no literal BitString fixed point
    is assumed. -/
structure ExtensionalSameInputCompiler
    (M : PolyDTMCandidate) where
  compile : Nat.Partrec.Code → Nat.Partrec.Code
  compile_computable : Computable compile
  circuitOf : Nat.Partrec.Code → CircuitK1.Circuit
  selfInput : Nat.Partrec.Code → BitString
  selfInput_ext :
    ∀ a b : Nat.Partrec.Code,
      Nat.Partrec.Code.eval a = Nat.Partrec.Code.eval b →
      selfInput a = selfInput b
  compile_realizes :
    ∀ c : Nat.Partrec.Code,
      selfInput (compile c) = encodeCircuit (circuitOf c)
  cook_levin_correct :
    ∀ c : Nat.Partrec.Code,
      SATBits CanonicalCircuitBits.circuitBitEncoding (encodeCircuit (circuitOf c)) ↔
        ¬ AcceptsAtDeclaredBound M (selfInput c)

theorem extensional_fixed_point
    {M : PolyDTMCandidate}
    (E : ExtensionalSameInputCompiler M) :
    ∃ c : Nat.Partrec.Code,
      Nat.Partrec.Code.eval c =
        Nat.Partrec.Code.eval (E.compile c) := by
  rcases Nat.Partrec.Code.fixed_point E.compile_computable with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

noncomputable def witnessOfExtensionalCompiler
    (M : PolyDTMCandidate)
    (E : ExtensionalSameInputCompiler M) : BitString :=
  let c := Classical.choose (extensional_fixed_point E)
  encodeCircuit (E.circuitOf c)

theorem witnessOfExtensionalCompiler_valid
    (M : PolyDTMCandidate)
    (E : ExtensionalSameInputCompiler M) :
    CanonicalSATValid (witnessOfExtensionalCompiler M E) := by
  unfold witnessOfExtensionalCompiler
  let c := Classical.choose (extensional_fixed_point E)
  exact ⟨E.circuitOf c, decodeCircuit_encode (E.circuitOf c)⟩

theorem witnessOfExtensionalCompiler_flip
    (M : PolyDTMCandidate)
    (E : ExtensionalSameInputCompiler M) :
    SATBits CanonicalCircuitBits.circuitBitEncoding (witnessOfExtensionalCompiler M E) ↔
      ¬ AcceptsAtDeclaredBound M (witnessOfExtensionalCompiler M E) := by
  unfold witnessOfExtensionalCompiler
  let c := Classical.choose (extensional_fixed_point E)
  have hc :
      Nat.Partrec.Code.eval c =
        Nat.Partrec.Code.eval (E.compile c) :=
    Classical.choose_spec (extensional_fixed_point E)
  have hsame :
      E.selfInput c = encodeCircuit (E.circuitOf c) := by
    calc
      E.selfInput c = E.selfInput (E.compile c) :=
        E.selfInput_ext c (E.compile c) hc
      _ = encodeCircuit (E.circuitOf c) := E.compile_realizes c
  simpa [hsame] using E.cook_levin_correct c

structure UniformExtensionalSameInputCompiler where
  compiler : ∀ M : PolyDTMCandidate, ExtensionalSameInputCompiler M

noncomputable def UniformExtensionalSameInputCompiler.toSameInputClosure
    (U : UniformExtensionalSameInputCompiler) : SameInputClosure where
  witness := fun M => witnessOfExtensionalCompiler M (U.compiler M)
  valid := fun M => witnessOfExtensionalCompiler_valid M (U.compiler M)
  simulation_exact := fun M =>
    witnessOfExtensionalCompiler_flip M (U.compiler M)

theorem uniform_extensional_compiler_gives_mismatch
    (U : UniformExtensionalSameInputCompiler)
    (M : PolyDTMCandidate) :
    P02UniversalFailureAlgebra.SemanticMismatch M (U.toSameInputClosure.witness M) :=
  sameInputClosure_gives_mismatch U.toSameInputClosure M

#print axioms MCore.Real.OpenMathCore.extensional_fixed_point
#print axioms MCore.Real.OpenMathCore.witnessOfExtensionalCompiler_valid
#print axioms MCore.Real.OpenMathCore.witnessOfExtensionalCompiler_flip
#print axioms MCore.Real.OpenMathCore.UniformExtensionalSameInputCompiler.toSameInputClosure

end MCore.Real.OpenMathCore
