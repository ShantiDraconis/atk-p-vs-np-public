import MCore.Real.PNPDiscovery.SourceGlobalBitOffset

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- Exact mechanical transport still needed: the local mismatch bit inside the
j-th encoded source-cell block must be the same global bit after prepending
the already-equal encoded clause prefix. -/
def SourceCellBitTransportGap : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y),
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let Fx := boundedExecTableauCNF_NTM N x tx
    let Fy := boundedExecTableauCNF_NTM N y ty
    let bx := sourceCellBitOffset N x tx W.j
    let by := sourceCellBitOffset N y ty W.j
    let ex := sourcePrefixBitEnd N x tx (W.j + 1)
    let ey := sourcePrefixBitEnd N y ty (W.j + 1)
    ∃ q : Nat,
      bx = by ∧
      Nat.min bx by ≤ q ∧
      q < Nat.min ex ey ∧
      (encodeCircuit (ntmCNFCircuit Fx)).getD q false ≠
        (encodeCircuit (ntmCNFCircuit Fy)).getD q false

/-- This is exactly the earlier SourceCellMismatchLocalizationGap, now with
the stronger start-offset equality made explicit. -/
theorem sourceCellBitTransport_closes_localization
    (H : SourceCellBitTransportGap) :
    SourceCellMismatchLocalizationGap := by
  intro M x y W
  rcases H M x y W with
    ⟨q, hStartEq, hStart, hEnd, hDiff⟩
  exact ⟨q, hStart, hEnd, hDiff⟩

/-- Once the mechanical transport closes, the SOURCE branch immediately
splits at the actual shared read-cone boundary. -/
theorem sourceTransport_visibility_split
    (H : SourceCellBitTransportGap)
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    ∃ q : Nat,
      let N := complementToNTMCandidate M
      let tx := M.timeBound x.length
      let ty := M.timeBound y.length
      let bx := sourceCellBitOffset N x tx W.j
      let by := sourceCellBitOffset N y ty W.j
      let ex := sourcePrefixBitEnd N x tx (W.j + 1)
      let ey := sourcePrefixBitEnd N y ty (W.j + 1)
      Nat.min bx by ≤ q ∧
      q < Nat.min ex ey ∧
      (q < SharedReadConePrefix M x y ∨
        SharedReadConePrefix M x y ≤ q) := by
  exact localizedSourceBit_visibility_split
    (sourceCellBitTransport_closes_localization H)
    M x y W

/-- If the transported mismatch is hidden from the shared cone, the surviving
condition is now purely arithmetic. -/
def SourceHiddenGrowthFrontier : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y)
    (q : Nat),
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let bx := sourceCellBitOffset N x tx W.j
    let by := sourceCellBitOffset N y ty W.j
    Nat.min bx by ≤ q →
    SharedReadConePrefix M x y ≤ q →
    Nat.min
      (M.timeBound x.length)
      (M.timeBound y.length) < q

theorem sourceHiddenGrowthFrontier_closed :
    SourceHiddenGrowthFrontier :=
  hiddenSourceGrowth_closed

#print axioms MCore.Real.PNPDiscovery.sourceCellBitTransport_closes_localization
#print axioms MCore.Real.PNPDiscovery.sourceTransport_visibility_split
#print axioms MCore.Real.PNPDiscovery.sourceHiddenGrowthFrontier_closed

end PNPDiscovery
end Real
end MCore
