import MCore.Real.PNPDiscovery.SourceOffsetLowerEnvelope
import MCore.Real.PNPDiscovery.SourceBitOffsets
import MCore.Real.PNPDiscovery.SuccessorClockEnvelope

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics
open PNPNTMTableauEncoding

/-- The source-cell bit offset is always within the full reduction encoding. -/
theorem sourceCellBitOffset_le_R_length
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (j : Nat)
    (hj : j < ntmRadius x (M.timeBound x.length)) :
    sourceCellBitOffset
        (complementToNTMCandidate M)
        x (M.timeBound x.length) j ≤
      (R_M M hTotal x).length := by
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  have hfull :
      fullSourceCellBitOffset N x t j =
        sourceCellBitOffset N x t j := by
    exact fullSourceCellBitOffset_eq_initial
      N x t j hj
  unfold fullSourceCellBitOffset tableauClauseBitOffset
  rw [hfull]
  unfold clauseBitOffset
  unfold R_M complementSemanticReduction
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  change
    (encodeCNFSpinePrefix
      ((boundedExecTableauCNF_NTM N x t).take
        (sourceCellClauseOffset N x t j))).length ≤
      (encodeCircuit
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM N x t))).length
  have hsplit :=
    encode_ntmCNFCircuit_split_at
      (boundedExecTableauCNF_NTM N x t)
      (sourceCellClauseOffset N x t j)
  rw [hsplit]
  simp

/-- At source index |x| the lower envelope already dominates |x| strictly:
there are |x| complete right-cell blocks before that boundary, each with
positive unary-encoding cost. -/
theorem inputLength_lt_sourceOffsetLowerEnvelope
    (M : PolyDTMCandidate)
    (x : BitString) :
    x.length <
      sourceCellOffsetLowerEnvelope
        M x.length (M.timeBound x.length) x.length := by
  unfold sourceCellOffsetLowerEnvelope
  dsimp
  have h48 : x.length < x.length * 48 + 1 := by
    cases x.length with
    | zero => simp
    | succ n =>
        omega
  omega

/-- The concrete complemented Cook--Levin reduction strictly increases
bitstring length on every input. -/
theorem R_M_strict_length_growth
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    x.length < (R_M M hTotal x).length := by
  have hj :
      x.length < ntmRadius x (M.timeBound x.length) := by
    simp [ntmRadius]
  have hLow :=
    sourceCellOffsetLowerEnvelope_le
      M x (M.timeBound x.length) x.length (Nat.le_of_lt hj)
  have hInside :=
    sourceCellBitOffset_le_R_length
      M hTotal x x.length hj
  have hInput :=
    inputLength_lt_sourceOffsetLowerEnvelope M x
  omega

/-- Orbit lengths therefore strictly increase at every step. -/
theorem orbit_length_strictly_increases
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    (orbit M hTotal seed n).length <
      (orbit M hTotal seed (n + 1)).length := by
  simpa [orbit, reductionMap_eq_R_M] using
    R_M_strict_length_growth
      M hTotal (orbit M hTotal seed n)

/-- Strict growth propagates over every positive gap. -/
theorem orbit_length_strict_mono
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    {i j : Nat}
    (hij : i < j) :
    (orbit M hTotal seed i).length <
      (orbit M hTotal seed j).length := by
  induction j with
  | zero =>
      omega
  | succ j ih =>
      by_cases hEq : i = j
      · subst i
        exact orbit_length_strictly_increases
          M hTotal seed j
      · have hij' : i < j := by omega
        exact lt_trans
          (ih hij')
          (orbit_length_strictly_increases
            M hTotal seed j)

/-- In particular no positive odd-separated orbit pair can have equal length. -/
theorem no_positive_odd_length_recurrence
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i d : Nat) :
    (orbit M hTotal seed (i + 1)).length ≠
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length := by
  have hlt :
      i + 1 < (i + 1) + (2 * d + 1) := by
    omega
  exact Nat.ne_of_lt
    (orbit_length_strict_mono
      M hTotal seed hlt)

#print axioms MCore.Real.PNPDiscovery.sourceCellBitOffset_le_R_length
#print axioms MCore.Real.PNPDiscovery.inputLength_lt_sourceOffsetLowerEnvelope
#print axioms MCore.Real.PNPDiscovery.R_M_strict_length_growth
#print axioms MCore.Real.PNPDiscovery.orbit_length_strictly_increases
#print axioms MCore.Real.PNPDiscovery.no_positive_odd_length_recurrence

end PNPDiscovery
end Real
end MCore
