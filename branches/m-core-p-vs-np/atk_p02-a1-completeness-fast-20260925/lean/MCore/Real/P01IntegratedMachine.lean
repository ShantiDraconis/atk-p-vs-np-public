import MCore.Real.CanonicalSATParserNTM
import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore
namespace Real
namespace P01IntegratedMachine

open CanonicalFinalProof
open CanonicalSATParserNTM
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalControl

/--
Fixed finite state layout for the integrated machine.
0..24   parser
25..36  witness preparation
37..44  physical verifier control
45      final accept
46      final reject
-/
abbrev IntegratedState := Fin 47

def parserState (q : Fin 25) : IntegratedState :=
  ⟨q.val, by omega⟩

def witnessState (q : Fin 12) : IntegratedState :=
  ⟨25 + q.val, by omega⟩

def verifierState (q : Fin 8) : IntegratedState :=
  ⟨37 + q.val, by omega⟩

def integratedAccept : IntegratedState := ⟨45, by decide⟩
def integratedReject : IntegratedState := ⟨46, by decide⟩

theorem parserState_injective :
    ∀ ⦃a b : Fin 25⦄, parserState a = parserState b → a = b := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun z : IntegratedState => z.val) h

theorem witnessState_injective :
    ∀ ⦃a b : Fin 12⦄, witnessState a = witnessState b → a = b := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [witnessState] at hv
  omega

theorem verifierState_injective :
    ∀ ⦃a b : Fin 8⦄, verifierState a = verifierState b → a = b := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [verifierState] at hv
  omega

theorem parser_witness_disjoint
    (p : Fin 25) (w : Fin 12) :
    parserState p ≠ witnessState w := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [parserState, witnessState] at hv
  omega

theorem parser_verifier_disjoint
    (p : Fin 25) (v : Fin 8) :
    parserState p ≠ verifierState v := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [parserState, verifierState] at hv
  omega

theorem witness_verifier_disjoint
    (w : Fin 12) (v : Fin 8) :
    witnessState w ≠ verifierState v := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [witnessState, verifierState] at hv
  omega

theorem parser_not_accept (p : Fin 25) :
    parserState p ≠ integratedAccept := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [parserState, integratedAccept] at hv
  omega

theorem witness_not_accept (w : Fin 12) :
    witnessState w ≠ integratedAccept := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [witnessState, integratedAccept] at hv
  omega

theorem verifier_not_accept (v : Fin 8) :
    verifierState v ≠ integratedAccept := by
  intro h
  have hv := congrArg (fun z : IntegratedState => z.val) h
  simp [verifierState, integratedAccept] at hv
  omega

theorem accept_ne_reject :
    integratedAccept ≠ integratedReject := by
  decide

/--
The fixed-control state-space part of T1-D is now explicit.  The remaining
construction obligation is semantic: bridge the terminal parser configuration
to witness preparation while restoring the canonical source layout, then bridge
the prepared tape to the physical verifier.
-/
structure IntegratedPhaseBridgeCertificate where
  parser_to_witness :
    ∀ q : Fin 25, parserNTM.accepting q = true →
      parserState q ≠ integratedReject
  witness_to_verifier :
    witnessState (11 : Fin 12) ≠ integratedReject
  verifier_to_terminal :
    verifierState halt ≠ integratedReject

def integratedPhaseBridgeCertificate : IntegratedPhaseBridgeCertificate where
  parser_to_witness := by
    intro q _
    intro h
    have hv := congrArg (fun z : IntegratedState => z.val) h
    simp [parserState, integratedReject] at hv
    omega
  witness_to_verifier := by
    intro h
    have hv := congrArg (fun z : IntegratedState => z.val) h
    simp [witnessState, integratedReject] at hv
    omega
  verifier_to_terminal := by
    intro h
    have hv := congrArg (fun z : IntegratedState => z.val) h
    simp [verifierState, integratedReject, halt] at hv
    omega

#print axioms MCore.Real.P01IntegratedMachine.parserState_injective
#print axioms MCore.Real.P01IntegratedMachine.witnessState_injective
#print axioms MCore.Real.P01IntegratedMachine.verifierState_injective
#print axioms MCore.Real.P01IntegratedMachine.integratedPhaseBridgeCertificate

end P01IntegratedMachine
end Real
end MCore
