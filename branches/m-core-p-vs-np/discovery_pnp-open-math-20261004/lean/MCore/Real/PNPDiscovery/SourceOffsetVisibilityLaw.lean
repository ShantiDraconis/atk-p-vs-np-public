import MCore.Real.PNPDiscovery.GlobalBreakSandwich
import MCore.Real.PNPDiscovery.FirstSourceMismatch
import MCore.Real.PNPDiscovery.SourcePrefixCoverageClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics
open PNPNTMTableauEncoding

/-- For a complete source mismatch witness, the two successor encodings agree
through the exact bit offset immediately before the mismatching source cell. -/
theorem sourceWitness_prefixEqual_beforeCell
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let b := sourceCellBitOffset N x tx W.j
    (R_M M hTotal x).take b =
      (R_M M hTotal y).take b := by
  dsimp
  let A : SourcePrefixLayoutAlignment M x y W.j :=
    { length_eq := W.length_eq
      clock_eq := W.clock_eq
      head_eq := W.head_eq
      source_eq := W.prefix_eq
      within_radius := by omega }
  have h :=
    sourcePrefixCoverage_closed M hTotal x y W.j A
  have hBoundary :
      sourcePrefixBitEnd
          (complementToNTMCandidate M)
          x (M.timeBound x.length) W.j =
        sourceCellBitOffset
          (complementToNTMCandidate M)
          x (M.timeBound x.length) W.j := by
    unfold sourcePrefixBitEnd tableauClauseBitOffset
    unfold sourceCellBitOffset
    unfold sourcePrefixClauseEnd sourceCellClauseOffset
    rfl
  simpa [hBoundary] using h

/-- Therefore the first break of the successor encodings lies strictly after
the start of the first mismatching source-cell block. -/
theorem firstGlobalBreak_after_sourceCellOffset
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (W : SourceMismatchWitness M x y)
    (hne : R_M M hTotal x ≠ R_M M hTotal y) :
    sourceCellBitOffset
        (complementToNTMCandidate M)
        x (M.timeBound x.length) W.j <
      firstPrefixBreak
        (R_M M hTotal x)
        (R_M M hTotal y)
        hne := by
  let b :=
    sourceCellBitOffset
      (complementToNTMCandidate M)
      x (M.timeBound x.length) W.j
  have hEq :=
    sourceWitness_prefixEqual_beforeCell M hTotal x y W
  by_contra hNot
  have hk :
      firstPrefixBreak
          (R_M M hTotal x)
          (R_M M hTotal y)
          hne ≤ b := by
    omega
  have hTake := congrArg
    (fun bs : BitString =>
      bs.take
        (firstPrefixBreak
          (R_M M hTotal x)
          (R_M M hTotal y)
          hne))
    hEq
  have hPrefix :
      (R_M M hTotal x).take
          (firstPrefixBreak
            (R_M M hTotal x)
            (R_M M hTotal y)
            hne) =
        (R_M M hTotal y).take
          (firstPrefixBreak
            (R_M M hTotal x)
            (R_M M hTotal y)
            hne) := by
    simpa [b, List.take_take, Nat.min_eq_left hk] using hTake
  exact (firstPrefixBreak_spec
    (R_M M hTotal x)
    (R_M M hTotal y)
    hne) hPrefix

/-- Main necessary law for an equal-length odd barrier pair:
the candidate's successor shared read cone must reach strictly beyond the bit
offset of the first mismatching source cell. -/
theorem barrier_equalLength_forces_sourceOffset_visible
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat)
    (hLen :
      (orbit M hTotal seed (i + 1)).length =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    let W :=
      barrierFirstSourceMismatchWitness
        M hTotal Hbar seed i d hLen
    sourceCellBitOffset
        (complementToNTMCandidate M)
        x (M.timeBound x.length) W.j <
      SuccessorSharedReadConePrefix M hTotal x y := by
  dsimp
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  let W :=
    barrierFirstSourceMismatchWitness
      M hTotal Hbar seed i d hLen
  let hne :
      R_M M hTotal x ≠ R_M M hTotal y :=
    barrier_successors_ne M hTotal Hbar seed i d
  have hLow :=
    firstGlobalBreak_after_sourceCellOffset
      M hTotal x y W hne
  have hHigh :=
    barrier_firstGlobalBreak_visible
      M hTotal Hbar seed i d
  simpa [successorFirstPrefixBreak, x, y, W, hne] using
    lt_of_lt_of_le hLow hHigh

/-- The same necessary law with the explicit polynomial successor-clock upper
envelope. -/
theorem barrier_equalLength_sourceOffset_lt_clockEnvelope
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat)
    (hLen :
      (orbit M hTotal seed (i + 1)).length =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    let W :=
      barrierFirstSourceMismatchWitness
        M hTotal Hbar seed i d hLen
    sourceCellBitOffset
        (complementToNTMCandidate M)
        x (M.timeBound x.length) W.j <
      successorSharedConeEnvelope M x y := by
  dsimp
  exact lt_of_lt_of_le
    (barrier_equalLength_forces_sourceOffset_visible
      M hTotal Hbar seed i d hLen)
    (successorSharedCone_le_envelope
      M hTotal
      (orbit M hTotal seed (i + 1))
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))))

#print axioms MCore.Real.PNPDiscovery.sourceWitness_prefixEqual_beforeCell
#print axioms MCore.Real.PNPDiscovery.firstGlobalBreak_after_sourceCellOffset
#print axioms MCore.Real.PNPDiscovery.barrier_equalLength_forces_sourceOffset_visible
#print axioms MCore.Real.PNPDiscovery.barrier_equalLength_sourceOffset_lt_clockEnvelope

end PNPDiscovery
end Real
end MCore
