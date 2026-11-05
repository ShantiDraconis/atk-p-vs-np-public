import MCore.Real.P02KleeneDefinednessFrontier
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose

namespace MCore
namespace Real
namespace P02ExactCompilerSemantics

open CanonicalFinalProof
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02KleeneBridge
open P02KleeneDefinednessFrontier
open P02BitStringNatCoding
open P02CodeSemanticInput
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose

/-- Exact meaning required from the proposed effective compiler.
The expected natural number is the canonical code of the Cook--Levin rejection
circuit built on the same extensional semantic input. -/
def CompilerSemantics
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) : Prop :=
  ∀ c : Nat.Partrec.Code,
    encodeBitsNat
      (encodeCircuit (rejectCircuit M (selfInput c))) ∈
        K.f c 0

/-- Exact compiler semantics already implies the previously separated
zero-totality obligation. -/
theorem compilerSemantics_implies_zeroTotal
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (hSem : CompilerSemantics M K) :
    CompilerZeroTotal K := by
  intro c
  exact Part.dom_iff_mem.mpr
    ⟨encodeBitsNat (encodeCircuit (rejectCircuit M (selfInput c))),
      hSem c⟩

/-- Therefore exact compiler semantics also closes the Kleene-definedness
frontier. -/
noncomputable theorem compilerSemantics_closes_definedness
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M)
    (hSem : CompilerSemantics M K) :
    KleeneDefinednessGap M K :=
  compilerZeroTotal_closes_definedness K
    (compilerSemantics_implies_zeroTotal hSem)

/-- A compiler satisfying the exact semantic specification yields the actual
same-input diagonal witness. This theorem exposes that the semantic compiler
specification contains the terminal P02 content; it is not a mere engineering
obligation. -/
noncomputable def compilerSemantics_toDiagonalWitness
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M)
    (hSem : CompilerSemantics M K) :
    DiagonalCounterexampleWitness M := by
  let c := Classical.choose (kleene_fixed_point K)
  have hfixed : Nat.Partrec.Code.eval c = K.f c :=
    Classical.choose_spec (kleene_fixed_point K)
  let x : BitString := encodeCircuit (rejectCircuit M (selfInput c))
  have hk : encodeBitsNat x ∈ K.f c 0 := by
    simpa [x] using hSem c
  have hc : encodeBitsNat x ∈ c.eval 0 := by
    rw [hfixed]
    exact hk
  have hself : selfInput c = x :=
    selfInput_of_mem_encode c x hc
  refine
    { bits := x
      valid := ?_
      flips := ?_ }
  · exact ⟨rejectCircuit M (selfInput c), by simp [x]⟩
  · have hCL :=
      rejectCircuit_cook_levin_correct
        boundedExecCorrectness_closed M (selfInput c)
    simpa [x, hself] using hCL

/-- Uniform exact compiler semantics is already sufficient for the full
pointwise lower-bound producer. -/
def UniformExactCompilerSemantics : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ K : EffectiveDiagonalCompiler M,
      CompilerSemantics M K

noncomputable theorem uniformExactCompilerSemantics_toDiagonalFamily
    (h : UniformExactCompilerSemantics) :
    DiagonalFamily := by
  classical
  exact
    { witness := fun M =>
        let K := Classical.choose (h M)
        let hK := Classical.choose_spec (h M)
        compilerSemantics_toDiagonalWitness M K hK }

theorem uniformExactCompilerSemantics_closes_P02
    (h : UniformExactCompilerSemantics) :
    P02TerminalFrontier.P02Target := by
  exact diagonal_family_closes_p02
    (uniformExactCompilerSemantics_toDiagonalFamily h)


/-- Audit endpoint: the exact compiler producer already contains the terminal
lower-bound content.  Once the existing P01 SAT-in-NP producer is supplied,
this object closes the internal P-vs-NP separation directly. -/
theorem uniformExactCompilerSemantics_closes_internal
    (hP01 : CanonicalSATBoundary.SATInNPGap circuitBitEncoding)
    (h : UniformExactCompilerSemantics) :
    PneqNP := by
  exact P02TerminalFrontier.p01_p02_close_internal_separation
    hP01
    (uniformExactCompilerSemantics_closes_P02 h)

#print axioms MCore.Real.P02ExactCompilerSemantics.compilerSemantics_implies_zeroTotal
#print axioms MCore.Real.P02ExactCompilerSemantics.compilerSemantics_closes_definedness
#print axioms MCore.Real.P02ExactCompilerSemantics.compilerSemantics_toDiagonalWitness
#print axioms MCore.Real.P02ExactCompilerSemantics.uniformExactCompilerSemantics_closes_P02
#print axioms MCore.Real.P02ExactCompilerSemantics.uniformExactCompilerSemantics_closes_internal

end P02ExactCompilerSemantics
end Real
end MCore
