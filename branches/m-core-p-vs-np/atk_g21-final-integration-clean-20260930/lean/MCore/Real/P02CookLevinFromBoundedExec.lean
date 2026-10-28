import MCore.Real.P02BoundedComputationClose
import MCore.Real.P02KleeneCookLevinBridge

namespace MCore
namespace Real
namespace P02CookLevinFromBoundedExec

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge
open P02BoundedComputationEncoding
open P02BoundedComputationClose

/-- Deterministic candidate with the same machine/clock and complemented
accepting-state predicate. -/
def complementCandidate (M : PolyDTMCandidate) : PolyDTMCandidate where
  stateCount := M.stateCount
  machine := M.machine
  blank_none := M.blank_none
  accepting := fun q => !(M.accepting q)
  timeBound := M.timeBound
  time_poly := M.time_poly

theorem complement_acceptsAtFuel_iff
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    AcceptsAtFuel (complementCandidate M) x t ↔
      ¬ AcceptsAtFuel M x t := by
  unfold AcceptsAtFuel complementCandidate
  simp

/-- Cook-Levin circuit for rejection at M's declared clock.  It is exactly the
existing bounded-execution tableau applied to the complemented candidate. -/
def rejectCircuit
    (M : PolyDTMCandidate) (x : BitString) : CircuitK1.Circuit :=
  boundedExecCircuit (complementCandidate M) x (M.timeBound x.length)

theorem rejectCircuit_cook_levin_correct
    (hBounded : BoundedExecCorrectness)
    (M : PolyDTMCandidate) (x : BitString) :
    SATTarget (encodeCircuit (rejectCircuit M x)) ↔
      ¬ AcceptsAtDeclaredBound M x := by
  have hbits :=
    boundedExecCorrectness_to_bits hBounded
      (complementCandidate M) x (M.timeBound x.length)
  have hcomp :=
    complement_acceptsAtFuel_iff M x (M.timeBound x.length)
  have h :=
    hbits.trans hcomp
  simpa [rejectCircuit, boundedExecBits, SATTarget,
    AcceptsAtDeclaredBound, AcceptsAtFuel] using h

/-- Once bounded-execution correctness is closed, Cook-Levin correctness is no
longer an independent OPEN_MATH field.  The only remaining field here is the
same-input transport from the Kleene fixed point. -/
structure SameInputTransport
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  selfInput : Nat.Partrec.Code → BitString
  same_input_of_fixed :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
        selfInput c = encodeCircuit (rejectCircuit M (selfInput c))

def dataOfBoundedExec
    (hBounded : BoundedExecCorrectness)
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (S : SameInputTransport M K) :
    CookLevinSameInputData M K where
  circuitOf := fun c => rejectCircuit M (S.selfInput c)
  selfInput := S.selfInput
  cook_levin_correct := by
    intro c
    exact rejectCircuit_cook_levin_correct hBounded M (S.selfInput c)
  same_input_of_fixed := by
    intro c hfixed
    exact S.same_input_of_fixed c hfixed

theorem flips_of_fixed_from_boundedExec
    (hBounded : BoundedExecCorrectness)
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (S : SameInputTransport M K)
    (c : Nat.Partrec.Code)
    (hfixed : Nat.Partrec.Code.eval c = K.f c) :
    SATTarget (encodeCircuit (rejectCircuit M (S.selfInput c))) ↔
      ¬ AcceptsAtDeclaredBound M
        (encodeCircuit (rejectCircuit M (S.selfInput c))) := by
  exact (dataOfBoundedExec hBounded S).flips_of_fixed c hfixed

/-- Existing transition soundness is already inhabited.  Therefore the
remaining bounded-execution delta is the tableau-completeness certificate. -/
theorem boundedExec_of_tableauCompleteness
    (C : TableauCompletenessCertificate) :
    BoundedExecCorrectness :=
  certificates_close_boundedExecCorrectness
    transitionSoundnessCertificate C

#print axioms MCore.Real.P02CookLevinFromBoundedExec.complement_acceptsAtFuel_iff
#print axioms MCore.Real.P02CookLevinFromBoundedExec.rejectCircuit_cook_levin_correct
#print axioms MCore.Real.P02CookLevinFromBoundedExec.dataOfBoundedExec
#print axioms MCore.Real.P02CookLevinFromBoundedExec.flips_of_fixed_from_boundedExec
#print axioms MCore.Real.P02CookLevinFromBoundedExec.boundedExec_of_tableauCompleteness

end P02CookLevinFromBoundedExec
end Real
end MCore
