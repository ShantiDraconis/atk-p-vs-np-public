import Mathlib.Computability.PartrecCode
import MCore.Real.P02KleeneCookLevinBridge

namespace MCore
namespace Real
namespace P02ExtensionalSameInputBridge

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge

/-- Non-literal self-reference interface. The fixed-point theorem supplies
equality of program semantics, and selfInput must respect that equality. -/
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
      SATTarget (encodeCircuit (circuitOf c)) ↔
        ¬ AcceptsAtDeclaredBound M (selfInput c)

theorem extensional_fixed_point
    {M : PolyDTMCandidate}
    (E : ExtensionalSameInputCompiler M) :
    ∃ c : Nat.Partrec.Code,
      Nat.Partrec.Code.eval c =
        Nat.Partrec.Code.eval (E.compile c) := by
  rcases Nat.Partrec.Code.fixed_point E.compile_computable with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

theorem same_input_at_fixed_point
    {M : PolyDTMCandidate}
    (E : ExtensionalSameInputCompiler M)
    (c : Nat.Partrec.Code)
    (hfixed :
      Nat.Partrec.Code.eval c =
        Nat.Partrec.Code.eval (E.compile c)) :
    E.selfInput c = encodeCircuit (E.circuitOf c) := by
  calc
    E.selfInput c = E.selfInput (E.compile c) :=
      E.selfInput_ext c (E.compile c) hfixed
    _ = encodeCircuit (E.circuitOf c) :=
      E.compile_realizes c

noncomputable def ExtensionalSameInputCompiler.toDiagonalWitness
    {M : PolyDTMCandidate}
    (E : ExtensionalSameInputCompiler M) :
    DiagonalCounterexampleWitness M := by
  let c := Classical.choose (extensional_fixed_point E)
  have hc :
      Nat.Partrec.Code.eval c =
        Nat.Partrec.Code.eval (E.compile c) :=
    Classical.choose_spec (extensional_fixed_point E)
  have hsame :
      E.selfInput c = encodeCircuit (E.circuitOf c) :=
    same_input_at_fixed_point E c hc
  refine
    { bits := encodeCircuit (E.circuitOf c)
      valid := ?_
      flips := ?_ }
  · exact ⟨E.circuitOf c, decodeCircuit_encode (E.circuitOf c)⟩
  · simpa [hsame] using E.cook_levin_correct c

structure UniformExtensionalSameInputCompiler where
  compiler :
    ∀ M : PolyDTMCandidate,
      ExtensionalSameInputCompiler M

noncomputable def UniformExtensionalSameInputCompiler.toDiagonalFamily
    (U : UniformExtensionalSameInputCompiler) :
    DiagonalFamily where
  witness := fun M => (U.compiler M).toDiagonalWitness

theorem uniform_extensional_bridge_closes_G21
    (U : UniformExtensionalSameInputCompiler) :
    G21Pointwise := by
  intro M
  let W := (U.compiler M).toDiagonalWitness
  exact ⟨W.bits, diagonal_witness_fails M W⟩

theorem uniform_extensional_bridge_closes_P02
    (U : UniformExtensionalSameInputCompiler) :
    P02TerminalFrontier.P02Target :=
  g21_pointwise_iff_p02_target.mp
    (uniform_extensional_bridge_closes_G21 U)

/- Firewall: only extensional equality of Code.eval is used here.
No universal literal BitString fixed point is assumed or derived. -/

#print axioms MCore.Real.P02ExtensionalSameInputBridge.extensional_fixed_point
#print axioms MCore.Real.P02ExtensionalSameInputBridge.same_input_at_fixed_point
#print axioms MCore.Real.P02ExtensionalSameInputBridge.ExtensionalSameInputCompiler.toDiagonalWitness
#print axioms MCore.Real.P02ExtensionalSameInputBridge.uniform_extensional_bridge_closes_P02

end P02ExtensionalSameInputBridge
end Real
end MCore
