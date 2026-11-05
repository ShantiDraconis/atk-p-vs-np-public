import Mathlib.Computability.PartrecCode
import MCore.Real.P02ExactCompilerSemantics

namespace MCore
namespace Real
namespace P02EffectiveCompilerConstruction

open CanonicalFinalProof
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02KleeneBridge
open P02KleeneDefinednessFrontier
open P02BitStringNatCoding
open P02CodeSemanticInput
open P02CookLevinFromBoundedExec
open P02ExactCompilerSemantics

/-- The exact natural result demanded from the diagonal compiler at coordinate 0. -/
def compilerValue
    (M : PolyDTMCandidate)
    (c : Nat.Partrec.Code) : Nat :=
  encodeBitsNat
    (encodeCircuit (rejectCircuit M (selfInput c)))

/-- Canonical total partial-function implementation once compilerValue itself
is known computable.  The second input is intentionally ignored. -/
def compilerPFun
    (M : PolyDTMCandidate) :
    Nat.Partrec.Code → Nat →. Nat :=
  fun c _ => Part.some (compilerValue M c)

/-- Unary computability of compilerValue is sufficient to prove the required
binary partial-recursiveness. -/
theorem compilerPFun_partrec₂
    (M : PolyDTMCandidate)
    (hComp : Computable (compilerValue M)) :
    Partrec₂ (compilerPFun M) := by
  have hPair :
      Computable (fun p : Nat.Partrec.Code × Nat =>
        compilerValue M p.1) :=
    hComp.comp Computable.fst
  have hTwo :
      Computable₂ (fun c : Nat.Partrec.Code => fun _ : Nat =>
        compilerValue M c) :=
    hPair.to₂
  simpa [compilerPFun] using hTwo.partrec₂

/-- Concrete EffectiveDiagonalCompiler obtained from a computable total value
function.  No Kleene theorem or P02 hypothesis is used in this constructor. -/
def effectiveCompilerOfComputable
    (M : PolyDTMCandidate)
    (hComp : Computable (compilerValue M)) :
    EffectiveDiagonalCompiler M where
  f := compilerPFun M
  partrec := compilerPFun_partrec₂ M hComp

/-- The concrete compiler satisfies the exact semantic specification by
construction. -/
theorem effectiveCompiler_semantics
    (M : PolyDTMCandidate)
    (hComp : Computable (compilerValue M)) :
    CompilerSemantics M (effectiveCompilerOfComputable M hComp) := by
  intro c
  simp [effectiveCompilerOfComputable, compilerPFun, compilerValue,
    CompilerSemantics]

/-- Therefore a uniform computability proof for compilerValue closes the exact
compiler producer. -/
def UniformCompilerValueComputable : Prop :=
  ∀ M : PolyDTMCandidate, Computable (compilerValue M)

theorem uniformCompilerValueComputable_implies_exact
    (h : UniformCompilerValueComputable) :
    UniformExactCompilerSemantics := by
  intro M
  let K := effectiveCompilerOfComputable M (h M)
  exact ⟨K, effectiveCompiler_semantics M (h M)⟩

/-- Conversely, exact compiler semantics implies unary computability of the
same total compilerValue.  This proves that the remaining obligation is not
hidden in the choice of K: it is exactly computability of compilerValue. -/
theorem exact_implies_compilerValueComputable
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M)
    (hSem : CompilerSemantics M K) :
    Computable (compilerValue M) := by
  have hAtZero :
      Partrec (fun c : Nat.Partrec.Code => K.f c 0) := by
    exact K.partrec.comp
      Computable.id
      (Computable.const 0)
  have hEq :
      (fun c : Nat.Partrec.Code => K.f c 0) =
        (fun c : Nat.Partrec.Code => Part.some (compilerValue M c)) := by
    funext c
    apply (Part.eq_some_iff).2
    simpa [CompilerSemantics, compilerValue] using hSem c
  rw [hEq] at hAtZero
  change Partrec (fun c : Nat.Partrec.Code =>
    Part.some (compilerValue M c))
  exact hAtZero

theorem uniformExact_iff_compilerValueComputable :
    UniformExactCompilerSemantics ↔ UniformCompilerValueComputable := by
  constructor
  · intro h M
    rcases h M with ⟨K, hSem⟩
    exact exact_implies_compilerValueComputable M K hSem
  · exact uniformCompilerValueComputable_implies_exact

/-- Terminal consequence, now factored through the single exact computability
obligation. -/
theorem uniformCompilerValueComputable_closes_P02
    (h : UniformCompilerValueComputable) :
    P02TerminalFrontier.P02Target :=
  uniformExactCompilerSemantics_closes_P02
    (uniformCompilerValueComputable_implies_exact h)

#print axioms MCore.Real.P02EffectiveCompilerConstruction.compilerPFun_partrec₂
#print axioms MCore.Real.P02EffectiveCompilerConstruction.effectiveCompiler_semantics
#print axioms MCore.Real.P02EffectiveCompilerConstruction.exact_implies_compilerValueComputable
#print axioms MCore.Real.P02EffectiveCompilerConstruction.uniformExact_iff_compilerValueComputable
#print axioms MCore.Real.P02EffectiveCompilerConstruction.uniformCompilerValueComputable_closes_P02

end P02EffectiveCompilerConstruction
end Real
end MCore
