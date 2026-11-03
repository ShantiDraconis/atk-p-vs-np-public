import MCore.Real.PNPDiscovery.SourceOffsetLowerEnvelope
import MCore.Real.PNPDiscovery.SourceCellBitTransportClosed
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics
open PNPNTMTableauEncoding

/-- The retained radius is always positive. -/
theorem ntmRadius_pos
    (x : BitString)
    (t : Nat) :
    0 < ntmRadius x t := by
  simp [ntmRadius]

/-- The bit offset immediately before right/source cell 0 is a prefix length
of the full reduction encoding, hence no larger than the full output length. -/
theorem sourceCell0BitOffset_le_R_length
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    sourceCellBitOffset
        (complementToNTMCandidate M)
        x (M.timeBound x.length) 0 ≤
      (R_M M hTotal x).length := by
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  have hrad : 0 < ntmRadius x t := ntmRadius_pos x t
  rcases encode_tableau_split_sourceCell N x t 0 hrad with
    ⟨prefix, suffix, hplen, hp, henc⟩
  unfold R_M
  change
    sourceCellBitOffset N x t 0 ≤
      (encodeCircuit
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM N x t))).length
  rw [henc, ← hplen]
  simp

/-- Crude but universal lower bound: before even reaching source cell 0,
the encoding contains at least the entire left region, with one positive-cost
symbol block per retained tape cell. -/
theorem inputLength_lt_sourceCell0OffsetLower
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    x.length <
      sourceCellOffsetLowerEnvelope M x.length t 0 := by
  unfold sourceCellOffsetLowerEnvelope
  dsimp
  have hr : x.length + t + 1 > x.length := by omega
  have hcell :
      0 < 3 *
          ntmLeftBase
            (complementToNTMCandidate M)
            (List.replicate x.length false)
            t + 48 := by
    omega
  have hmul :
      x.length <
        (x.length + t + 1) *
          (3 *
            ntmLeftBase
              (complementToNTMCandidate M)
              (List.replicate x.length false)
              t + 48) := by
    have hone :
        1 ≤
          3 *
            ntmLeftBase
              (complementToNTMCandidate M)
              (List.replicate x.length false)
              t + 48 := by
      omega
    nlinarith
  omega

/-- The source-cell-0 lower envelope is below the actual cell-0 bit offset. -/
theorem sourceCell0Lower_le_actualOffset
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    sourceCellOffsetLowerEnvelope M x.length t 0 ≤
      sourceCellBitOffset
        (complementToNTMCandidate M)
        x t 0 := by
  apply sourceCellOffsetLowerEnvelope_le
  simp [ntmRadius]

/-- Critical discovery result: every concrete complemented Cook--Levin
reduction output is strictly longer than its source. -/
theorem R_M_strict_length_growth
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    x.length < (R_M M hTotal x).length := by
  let t := M.timeBound x.length
  have h1 :
      x.length <
        sourceCellOffsetLowerEnvelope M x.length t 0 :=
    inputLength_lt_sourceCell0OffsetLower M x t
  have h2 :
      sourceCellOffsetLowerEnvelope M x.length t 0 ≤
        sourceCellBitOffset
          (complementToNTMCandidate M)
          x t 0 :=
    sourceCell0Lower_le_actualOffset M x t
  have h3 :
      sourceCellBitOffset
          (complementToNTMCandidate M)
          x t 0 ≤
        (R_M M hTotal x).length := by
    simpa [t] using sourceCell0BitOffset_le_R_length M hTotal x
  omega

/-- Consequently orbit lengths are strictly increasing at every positive step. -/
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

/-- Any later orbit point has strictly larger length. -/
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
        simpa using orbit_length_strictly_increases M hTotal seed j
      · have hij' : i < j := by omega
        have hprev := ih hij'
        have hstep := orbit_length_strictly_increases M hTotal seed j
        omega

/-- In particular, no odd-separated positive orbit pair can have equal length. -/
theorem no_positive_odd_length_recurrence
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i d : Nat) :
    (orbit M hTotal seed (i + 1)).length ≠
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length := by
  have hidx :
      i + 1 < (i + 1) + (2 * d + 1) := by omega
  have hlt :=
    orbit_length_strict_mono M hTotal seed hidx
  omega

#print axioms MCore.Real.PNPDiscovery.R_M_strict_length_growth
#print axioms MCore.Real.PNPDiscovery.orbit_length_strictly_increases
#print axioms MCore.Real.PNPDiscovery.orbit_length_strict_mono
#print axioms MCore.Real.PNPDiscovery.no_positive_odd_length_recurrence

end PNPDiscovery
end Real
end MCore
