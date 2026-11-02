import MCore.Real.P02TableauCompletenessClose
import MCore.Real.P02SemanticFlipCore

namespace MCore
namespace Real
namespace P02AntiTableau

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02TableauCompletenessClose
open P02SemanticFlipCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

/-- Same deterministic machine and polynomial clock, with only the final
acceptance predicate complemented. -/
def complementCandidate
    (M : PolyDTMCandidate) :
    PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := fun q => !(M.accepting q)
    timeBound := M.timeBound
    time_poly := M.time_poly }

@[simp] theorem complementCandidate_machine
    (M : PolyDTMCandidate) :
    (complementCandidate M).machine = M.machine := rfl

@[simp] theorem complementCandidate_timeBound
    (M : PolyDTMCandidate) :
    (complementCandidate M).timeBound = M.timeBound := rfl

theorem complement_acceptsAtFuel_iff
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    AcceptsAtFuel (complementCandidate M) x t ↔
      M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state ≠ true := by
  unfold AcceptsAtFuel complementCandidate
  change
    (!(M.accepting
      (M.machine.run t
        (initialTMConfig M.machine x)).state)) = true ↔
      M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state ≠ true
  cases h :
      M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state <;>
    simp [h]

def antiTableauCircuit
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) : CircuitK1.Circuit :=
  boundedExecCircuit (complementCandidate M) x t

def antiTableauBits
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) : BitString :=
  encodeCircuit (antiTableauCircuit M x t)

theorem antiTableauBits_valid
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    ∃ phi : CircuitK1.Circuit,
      decodeCircuit (antiTableauBits M x t) = some phi := by
  refine ⟨antiTableauCircuit M x t, ?_⟩
  exact decodeCircuit_encode _

theorem antiTableauBits_sat_iff_not_acceptsAtFuel
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    SATTarget (antiTableauBits M x t) ↔
      M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state ≠ true := by
  change
    SATBits circuitBitEncoding
        (encodeCircuit (antiTableauCircuit M x t)) ↔ _
  rw [encoded_sat_equivalence]
  change
    SATLanguage
        (boundedExecCircuit (complementCandidate M) x t) ↔ _
  rw [boundedExecCorrectness_closed
    (complementCandidate M) x t]
  exact complement_acceptsAtFuel_iff M x t

def antiDeclaredBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  antiTableauBits M x (M.timeBound x.length)

theorem antiDeclaredBits_valid
    (M : PolyDTMCandidate)
    (x : BitString) :
    ∃ phi : CircuitK1.Circuit,
      decodeCircuit (antiDeclaredBits M x) = some phi := by
  exact antiTableauBits_valid M x (M.timeBound x.length)

theorem antiDeclaredBits_flip_source
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (antiDeclaredBits M x) ↔
      ¬ DeclaredAccepts M x := by
  unfold antiDeclaredBits DeclaredAccepts
  exact antiTableauBits_sat_iff_not_acceptsAtFuel
    M x (M.timeBound x.length)

/-- Extensional same-input transport is the only extra datum needed to turn
the anti-tableau source law into the exact semantic flip required by P02. -/
structure SameInputTransport
    (M : PolyDTMCandidate) where
  source : BitString
  same_input :
    antiDeclaredBits M source = source

theorem SameInputTransport.semanticFlip
    {M : PolyDTMCandidate}
    (T : SameInputTransport M) :
    SemanticFlip M T.source := by
  unfold SemanticFlip
  simpa [T.same_input] using
    antiDeclaredBits_flip_source M T.source

theorem same_input_transport_implies_total_semantic_flip_core
    (H :
      ∀ M : PolyDTMCandidate,
        P02TotalCandidateSemanticCore.DeclaredClockTotal M →
          Nonempty (SameInputTransport M)) :
    TotalCandidateSemanticFlipCore := by
  intro M hTotal
  rcases H M hTotal with ⟨T⟩
  exact ⟨T.source, T.semanticFlip⟩

#print axioms MCore.Real.P02AntiTableau.complement_acceptsAtFuel_iff
#print axioms MCore.Real.P02AntiTableau.antiTableauBits_sat_iff_not_acceptsAtFuel
#print axioms MCore.Real.P02AntiTableau.antiDeclaredBits_flip_source
#print axioms MCore.Real.P02AntiTableau.SameInputTransport.semanticFlip
#print axioms MCore.Real.P02AntiTableau.same_input_transport_implies_total_semantic_flip_core

end P02AntiTableau
end Real
end MCore
