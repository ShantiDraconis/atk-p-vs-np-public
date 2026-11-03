import P02.LANE4.AUX.R4_FINAL
import P02.LANE4.AUX.R4_INITIAL_INJECTIVE
import MCore.Real.P01PhysicalVerifierFoundations
import MCore.Real.P02ComplementRunRealization
import MCore.Real.PNPNTMTableauClosure

namespace P02
namespace LANE4
namespace AUX
namespace R5_PAIR_INJECTIVE

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding
open MCore.Real.PNPNTMTableauClosure
open MCore.Real.P02ComplementRunRealization

/-- Read the variable number of the first literal of the first clause.
The default value is irrelevant for the head block, which is nonempty. -/
def cnfFirstVar : NTMCNF → Nat
  | [] => 0
  | [] :: _ => 0
  | (l :: _) :: _ => l.var

theorem cnfFirstVar_setSymbol
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    cnfFirstVar (ntmSetSymbolClauses [] varAt target) = varAt none := by
  fin_cases target <;>
    simp [cnfFirstVar, ntmSetSymbolClauses, ntmAlphabet,
      ntmLitFor, ntmPos, ntmNeg]

/-- The same fixed-position head extractor works on the complete tableau,
because the initial block is the literal prefix of the tableau. -/
theorem boundedExecTableau_extract_head
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ((boundedExecTableauCNF_NTM M x t).drop (M.stateCount + 1)).take 3 =
      ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head := by
  simp [boundedExecTableauCNF_NTM, ntmInitialCNF,
    R2_R4_RADIUS.ntmSetStateClauses_length,
    R2_R4_RADIUS.ntmSetSymbolClauses_length]

/-- Equality of complete tableaux, even at different fuel values, determines
the fuel from the variable number in the first head clause. -/
theorem boundedExecTableau_eq_implies_time_eq
    {M : PolyNTMCandidate}
    {x y : BitString}
    {tx ty : Nat}
    (h :
      boundedExecTableauCNF_NTM M x tx =
      boundedExecTableauCNF_NTM M y ty) :
    tx = ty := by
  have hb := congrArg
    (fun f : NTMCNF => (f.drop (M.stateCount + 1)).take 3) h
  rw [boundedExecTableau_extract_head M x tx,
      boundedExecTableau_extract_head M y ty] at hb
  have hv := congrArg cnfFirstVar hb
  rw [cnfFirstVar_setSymbol, cnfFirstVar_setSymbol] at hv
  simp [ntmHeadVar, ntmHeadBase, ntmStateSlots, ntmStateCount,
    ntmSymbolCode] at hv
  omega

/-- Strong structural form of R4: the bounded tableau encoding is injective
in the pair (source,fuel). -/
theorem boundedExecTableau_pair_injective
    (M : PolyNTMCandidate)
    {x y : BitString}
    {tx ty : Nat}
    (h :
      boundedExecTableauCNF_NTM M x tx =
      boundedExecTableauCNF_NTM M y ty) :
    tx = ty ∧ x = y := by
  have ht := boundedExecTableau_eq_implies_time_eq h
  subst ty
  have hinit := R4_FINAL.tableau_initial_eq_of_whole h
  have hxy :=
    R4_INITIAL_INJECTIVE.ntmInitialCNF_injective_fixed M tx hinit
  exact ⟨rfl, hxy⟩

/-- Strong structural form at Circuit level. -/
theorem boundedExecCircuit_pair_injective
    (M : PolyNTMCandidate)
    {x y : BitString}
    {tx ty : Nat}
    (h :
      boundedExecCircuit_NTM M x tx =
      boundedExecCircuit_NTM M y ty) :
    tx = ty ∧ x = y := by
  have htab :
      boundedExecTableauCNF_NTM M x tx =
      boundedExecTableauCNF_NTM M y ty := by
    apply R1_R3_REAL.ntmCNFCircuit_injective
    simpa [boundedExecCircuit_NTM] using h
  exact boundedExecTableau_pair_injective M htab

/-- Exact unfolding of the concrete complement reduction. -/
theorem complement_reduce_def
    (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (x : BitString) :
    (complementSemanticReduction M hTotal).reduce x =
      P01PhysicalVerifierFoundations.encodeCircuit
        (boundedExecCircuit_NTM
          (complementToNTMCandidate M)
          x
          (M.timeBound x.length)) := by
  rfl

/-- R5: the concrete complement Cook--Levin reduction is injective on source
bitstrings.  No monotonicity or injectivity assumption on timeBound is used:
the encoded tableau itself recovers both fuel and source. -/
theorem reduce_M_injective_final
    (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M) :
    Function.Injective (complementSemanticReduction M hTotal).reduce := by
  intro x y h
  rw [complement_reduce_def M hTotal x,
      complement_reduce_def M hTotal y] at h
  have hc :
      boundedExecCircuit_NTM
          (complementToNTMCandidate M) x (M.timeBound x.length) =
      boundedExecCircuit_NTM
          (complementToNTMCandidate M) y (M.timeBound y.length) := by
    exact P01PhysicalVerifierFoundations.encodeCircuit_injective h
  exact
    (boundedExecCircuit_pair_injective
      (complementToNTMCandidate M) hc).2

#print axioms P02.LANE4.AUX.R5_PAIR_INJECTIVE.boundedExecTableau_eq_implies_time_eq
#print axioms P02.LANE4.AUX.R5_PAIR_INJECTIVE.boundedExecTableau_pair_injective
#print axioms P02.LANE4.AUX.R5_PAIR_INJECTIVE.boundedExecCircuit_pair_injective
#print axioms P02.LANE4.AUX.R5_PAIR_INJECTIVE.reduce_M_injective_final

end R5_PAIR_INJECTIVE
end AUX
end LANE4
end P02
