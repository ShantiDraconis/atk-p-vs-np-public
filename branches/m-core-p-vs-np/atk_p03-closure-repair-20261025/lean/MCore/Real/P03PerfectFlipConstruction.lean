import MCore.Real.P03PerfectFlipDichotomy
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace P03PerfectFlipConstruction

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02TableauDynamics
open PNPNTMTableauEncoding
open SourceRecovery
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

/-- Every concrete bounded NTM tableau CNF is nonempty because it contains the
final-acceptance clause. -/
theorem boundedExecTableauCNF_NTM_ne_nil
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    boundedExecTableauCNF_NTM M x t ≠ [] := by
  intro h
  have hlen :
      0 < (boundedExecTableauCNF_NTM M x t).length := by
    unfold boundedExecTableauCNF_NTM ntmFinalAcceptanceCNF
    simp
  rw [h] at hlen
  simp at hlen

/-- Consequently the circuit emitted by the concrete tableau is always rooted
at AND. -/
theorem boundedExecCircuit_NTM_is_and
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ∃ a b : CircuitK1.Circuit,
      boundedExecCircuit_NTM M x t = .and a b := by
  unfold boundedExecCircuit_NTM
  cases hF : boundedExecTableauCNF_NTM M x t with
  | nil =>
      exfalso
      exact boundedExecTableauCNF_NTM_ne_nil M x t hF
  | cons c cs =>
      exact ⟨ntmClauseCircuit c, ntmCNFCircuit cs, by
        simp [ntmCNFCircuit]⟩

/-- Every real reduction image starts with the fixed AND tag 100. -/
theorem R_M_fixed_prefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ tail : BitString,
      R_M M hTotal x = [true, false, false] ++ tail := by
  rcases boundedExecCircuit_NTM_is_and
      (complementToNTMCandidate M)
      x
      (M.timeBound x.length) with ⟨a, b, hab⟩
  refine ⟨encodeCircuit a ++ encodeCircuit b, ?_⟩
  unfold R_M complementSemanticReduction
  change
    encodeCircuit
      (PNPNTMTableauClosure.concreteNTMTableauProducer.circuit
        (complementRunRealization M hTotal).candidate
        x
        ((complementRunRealization M hTotal).candidate.timeBound x.length))
      = _
  simp [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate, hab,
    encodeCircuit]

/-- A classifier depending only on the first three bits is constant on the
entire real reduction range. -/
theorem range_first3_classifier_constant
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (f : Bool → Bool → Bool → Bool)
    (x y : BitString) :
    (match R_M M hTotal x with
      | a :: b :: c :: _ => f a b c
      | _ => false) =
    (match R_M M hTotal y with
      | a :: b :: c :: _ => f a b c
      | _ => false) := by
  rcases R_M_fixed_prefix M hTotal x with ⟨tx, hx⟩
  rcases R_M_fixed_prefix M hTotal y with ⟨ty, hy⟩
  simp [hx, hy]

/-- The source decoder is a genuine left inverse on every real range point. -/
theorem R_M_source_recover
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeSourceBits
        (complementToNTMCandidate M)
        x.length
        (M.timeBound x.length)
        (R_M M hTotal x) = some x := by
  simpa [R_M] using decodeSource_reduce M hTotal x

/--
The remaining constructive route to a real perfect flip therefore cannot be a
fixed-prefix classifier.  A sufficient concrete mechanism is an operational
machine that, on a genuine range point, recovers the embedded source and
returns the negation of its own declared acceptance on that source.

This proposition is deliberately stated at the semantic boundary only; no
inhabitant is postulated.
-/
def SourceRecursiveFlipLaw
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ x : BitString,
    DeclaredAccepts M (R_M M hTotal x) ↔
      ¬ DeclaredAccepts M x

theorem sourceRecursiveFlipLaw_iff_perfectFlip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    SourceRecursiveFlipLaw M hTotal ↔ PerfectFlip M hTotal := by
  rfl

#print axioms MCore.Real.P03PerfectFlipConstruction.boundedExecTableauCNF_NTM_ne_nil
#print axioms MCore.Real.P03PerfectFlipConstruction.boundedExecCircuit_NTM_is_and
#print axioms MCore.Real.P03PerfectFlipConstruction.R_M_fixed_prefix
#print axioms MCore.Real.P03PerfectFlipConstruction.range_first3_classifier_constant
#print axioms MCore.Real.P03PerfectFlipConstruction.R_M_source_recover
#print axioms MCore.Real.P03PerfectFlipConstruction.sourceRecursiveFlipLaw_iff_perfectFlip

end P03PerfectFlipConstruction
end Real
end MCore
