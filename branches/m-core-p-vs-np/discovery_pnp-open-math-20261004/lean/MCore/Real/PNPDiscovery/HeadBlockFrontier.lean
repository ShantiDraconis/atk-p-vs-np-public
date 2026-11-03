import MCore.Real.PNPDiscovery.EncodingSpine

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open P02ComplementRunRealization
open P02TableauDynamics

/-- The only source datum used by the time-zero head block. -/
def sourceHeadSymbol (x : BitString) : Option Bool :=
  (inputTape x).head

@[simp] theorem sourceHeadSymbol_nil :
    sourceHeadSymbol [] = none := by
  rfl

@[simp] theorem sourceHeadSymbol_cons
    (b : Bool) (bs : BitString) :
    sourceHeadSymbol (b :: bs) = some b := by
  rfl

/-- Exact time-zero head CNF block. -/
def initialHeadBlock
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  ntmSetSymbolClauses []
    (ntmHeadVar M t 0)
    (sourceHeadSymbol x)

/-- The head block depends only on clock and first source symbol. -/
theorem initialHeadBlock_eq_of_clock_head
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hClock : t = u)
    (hHead : sourceHeadSymbol x = sourceHeadSymbol y) :
    initialHeadBlock M x t =
      initialHeadBlock M y u := by
  subst u
  unfold initialHeadBlock
  rw [hHead]

/-- Exact decomposition after the stable state block: head block comes next. -/
theorem boundedExecTableau_state_head_split
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ∃ rest : NTMCNF,
      boundedExecTableauCNF_NTM M x t =
        ntmSetStateClauses [] M t 0 M.machine.initial ++
        initialHeadBlock M x t ++
        rest := by
  refine ⟨
    (List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetLeftCell [] M x t 0 i
        ((inputTape x).left.getD i M.machine.blank)) ++
    (List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank)) ++
    ntmTransitionsCNF M x t ++
    ntmFinalAcceptanceCNF M t, ?_⟩
  simp [boundedExecTableauCNF_NTM, ntmInitialCNF,
    initialHeadBlock, sourceHeadSymbol, List.append_assoc]

/-- Candidate/clock/head-specific prefix extending beyond the universal state
block. -/
def initialStateHeadEncodingPrefix
    (M : PolyDTMCandidate)
    (t : Nat)
    (a : Option Bool) : BitString :=
  let N := complementToNTMCandidate M
  encodeCNFSpinePrefix
    (ntmSetStateClauses [] N 0 0 N.machine.initial) ++
  encodeCNFSpinePrefix
    (ntmSetSymbolClauses [] (ntmHeadVar N t 0) a)

/-- If two inputs have equal declared clock and equal initial head symbol,
their reductions agree throughout the complete state+head encoding prefix. -/
theorem reduction_stateHead_prefix_eq
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (hClock :
      M.timeBound x.length = M.timeBound y.length)
    (hHead :
      sourceHeadSymbol x = sourceHeadSymbol y) :
    let k :=
      (initialStateHeadEncodingPrefix M
        (M.timeBound x.length)
        (sourceHeadSymbol x)).length
    (R_M M hTotal x).take k =
      (R_M M hTotal y).take k := by
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  have hty : M.timeBound y.length = t := by
    simpa [t] using hClock.symm
  rcases boundedExecTableau_state_head_split N x t with
    ⟨rx, hx⟩
  rcases boundedExecTableau_state_head_split N y t with
    ⟨ry, hy⟩
  have hState :
      ntmSetStateClauses [] N t 0 N.machine.initial =
        ntmSetStateClauses [] N 0 0 N.machine.initial :=
    initialStateClauses_clock_independent N t 0
  have hHeadBlock :
      initialHeadBlock N x t = initialHeadBlock N y t :=
    initialHeadBlock_eq_of_clock_head N x y t t rfl hHead
  unfold R_M complementSemanticReduction
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  change
    (encodeCircuit (boundedExecCircuit_NTM N x t)).take
        (initialStateHeadEncodingPrefix M t (sourceHeadSymbol x)).length =
      (encodeCircuit (boundedExecCircuit_NTM N y t)).take
        (initialStateHeadEncodingPrefix M t (sourceHeadSymbol x)).length
  unfold boundedExecCircuit_NTM
  rw [hx, hy]
  simp only [List.append_assoc]
  rw [encode_ntmCNFCircuit_append, encode_ntmCNFCircuit_append]
  rw [hState]
  rw [hHeadBlock]
  unfold initialStateHeadEncodingPrefix
  simp [N, t, initialHeadBlock, List.append_assoc]

/-- The next material split after the state block is therefore explicit:
clock equality + first-symbol equality are sufficient to extend the common
encoding prefix through the complete head block. -/
structure HeadAlignment
    (M : PolyDTMCandidate)
    (x y : BitString) : Prop where
  clock :
    M.timeBound x.length = M.timeBound y.length
  head :
    sourceHeadSymbol x = sourceHeadSymbol y

theorem headAlignment_gives_prefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (H : HeadAlignment M x y) :
    let k :=
      (initialStateHeadEncodingPrefix M
        (M.timeBound x.length)
        (sourceHeadSymbol x)).length
    (R_M M hTotal x).take k =
      (R_M M hTotal y).take k :=
  reduction_stateHead_prefix_eq M hTotal x y H.clock H.head

#print axioms MCore.Real.PNPDiscovery.initialHeadBlock_eq_of_clock_head
#print axioms MCore.Real.PNPDiscovery.boundedExecTableau_state_head_split
#print axioms MCore.Real.PNPDiscovery.reduction_stateHead_prefix_eq
#print axioms MCore.Real.PNPDiscovery.headAlignment_gives_prefix

end PNPDiscovery
end Real
end MCore
