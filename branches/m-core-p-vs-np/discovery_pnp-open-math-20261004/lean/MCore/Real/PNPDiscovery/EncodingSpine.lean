import MCore.Real.PNPDiscovery.ParityDistinguishingBit
import MCore.Real.PNPNTMTableauEncoding

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open P02TableauDynamics
open P02ComplementRunRealization
open P03PerfectFlipConstruction

/-- Encoding prefix contributed by a CNF list before its final recursive tail. -/
def encodeCNFSpinePrefix : NTMCNF → BitString
  | [] => []
  | c :: cs =>
      [true, false, false] ++
        encodeCircuit (ntmClauseCircuit c) ++
        encodeCNFSpinePrefix cs

/-- Exact decomposition of canonical CNF encoding across list append. -/
theorem encode_ntmCNFCircuit_append
    (F G : NTMCNF) :
    encodeCircuit (ntmCNFCircuit (F ++ G)) =
      encodeCNFSpinePrefix F ++
        encodeCircuit (ntmCNFCircuit G) := by
  induction F with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [ntmCNFCircuit, encodeCircuit, encodeCNFSpinePrefix,
        ih, List.append_assoc]

/-- At tableau time zero the state variable indices do not depend on the
declared clock parameter. -/
theorem ntmStateVar_time0_independent
    (M : PolyNTMCandidate)
    (t u : Nat)
    (q : Fin (M.stateCount + 1)) :
    ntmStateVar M t 0 q = ntmStateVar M u 0 q := by
  simp [ntmStateVar]

/-- Consequently the entire initial-state clause block is independent of the
clock. -/
theorem initialStateClauses_clock_independent
    (M : PolyNTMCandidate)
    (t u : Nat) :
    ntmSetStateClauses [] M t 0 M.machine.initial =
      ntmSetStateClauses [] M u 0 M.machine.initial := by
  simp [ntmSetStateClauses, ntmStateVar]

/-- Canonical candidate-only state prefix used by every reduction output. -/
def initialStateEncodingPrefix
    (M : PolyDTMCandidate) : BitString :=
  encodeCNFSpinePrefix
    (ntmSetStateClauses []
      (complementToNTMCandidate M)
      0 0
      (complementToNTMCandidate M).machine.initial)

/-- The bounded tableau starts with the state block, followed by head/left/right
and transition/final material. -/
theorem boundedExecTableau_stateBlock_split
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ∃ rest : NTMCNF,
      boundedExecTableauCNF_NTM M x t =
        ntmSetStateClauses [] M t 0 M.machine.initial ++ rest := by
  refine ⟨
    ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
    (List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetLeftCell [] M x t 0 i
        ((inputTape x).left.getD i M.machine.blank)) ++
    (List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank)) ++
    ntmTransitionsCNF M x t ++
    ntmFinalAcceptanceCNF M t, ?_⟩
  simp [boundedExecTableauCNF_NTM, ntmInitialCNF, List.append_assoc]

/-- Every complemented Cook--Levin reduction begins with the entire
candidate-only initial-state encoding prefix. -/
theorem reduction_has_initialStateEncodingPrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ tail : BitString,
      R_M M hTotal x =
        initialStateEncodingPrefix M ++ tail := by
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  rcases boundedExecTableau_stateBlock_split N x t with ⟨rest, hsplit⟩
  refine ⟨encodeCircuit (ntmCNFCircuit rest), ?_⟩
  unfold R_M complementSemanticReduction
  change
    encodeCircuit
      (PNPNTMTableauClosure.concreteNTMTableauProducer.circuit
        (complementRunRealization M hTotal).candidate
        x
        ((complementRunRealization M hTotal).candidate.timeBound x.length)) =
      initialStateEncodingPrefix M ++
        encodeCircuit (ntmCNFCircuit rest)
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  change
    encodeCircuit (boundedExecCircuit_NTM N x t) =
      initialStateEncodingPrefix M ++
        encodeCircuit (ntmCNFCircuit rest)
  unfold boundedExecCircuit_NTM
  rw [hsplit]
  rw [encode_ntmCNFCircuit_append]
  unfold initialStateEncodingPrefix
  have hclock :
      ntmSetStateClauses [] N t 0 N.machine.initial =
        ntmSetStateClauses [] N 0 0 N.machine.initial :=
    initialStateClauses_clock_independent N t 0
  rw [hclock]

/-- The whole candidate-only state block is therefore a certified stable
prefix, not merely the three-bit AND tag. -/
theorem stablePrefix_initialStateBlock
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    StablePrefixAt M hTotal
      (initialStateEncodingPrefix M).length := by
  intro x y
  rcases reduction_has_initialStateEncodingPrefix M hTotal x with ⟨tx, hx⟩
  rcases reduction_has_initialStateEncodingPrefix M hTotal y with ⟨ty, hy⟩
  simp [hx, hy]

/-- Barrier pressure now starts only after the entire initial-state block. -/
theorem parityBarrier_after_initialStateBlock
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    (initialStateEncodingPrefix M).length <
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  exact parityBarrier_beats_every_stablePrefix
    M hTotal H seed i d
    (initialStateEncodingPrefix M).length
    (stablePrefix_initialStateBlock M hTotal)

#print axioms MCore.Real.PNPDiscovery.encode_ntmCNFCircuit_append
#print axioms MCore.Real.PNPDiscovery.initialStateClauses_clock_independent
#print axioms MCore.Real.PNPDiscovery.reduction_has_initialStateEncodingPrefix
#print axioms MCore.Real.PNPDiscovery.stablePrefix_initialStateBlock
#print axioms MCore.Real.PNPDiscovery.parityBarrier_after_initialStateBlock

end PNPDiscovery
end Real
end MCore
