import MCore.Real.PNPDiscovery.FiniteBitMismatchClosed
import MCore.Real.PNPDiscovery.SourceBitOffsets
import MCore.Real.PNPDiscovery.ReadCone

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Pure arithmetic split at the exact candidate read-cone boundary. -/
theorem bitBeforeSharedCone_or_after
    (M : PolyDTMCandidate)
    (x y : BitString)
    (q : Nat) :
    q < SharedReadConePrefix M x y ∨
      SharedReadConePrefix M x y ≤ q := by
  omega

/-- Concrete SOURCE witness produced after all layout alignment before cell j. -/
structure SourceMismatchWitness
    (M : PolyDTMCandidate)
    (x y : BitString) where
  j : Nat
  length_eq : x.length = y.length
  clock_eq :
    M.timeBound x.length = M.timeBound y.length
  head_eq :
    sourceHeadSymbol x = sourceHeadSymbol y
  prefix_eq :
    SourceRightPrefixAligned x y j
  source_diff :
    sourceRightSymbol x j ≠ sourceRightSymbol y j
  in_radius :
    j + 1 ≤ ntmRadius x (M.timeBound x.length)

/-- Encoded mismatch payload for one concrete source-cell witness. -/
structure EncodedSourceMismatch
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) where
  sx : BitString
  sy : BitString
  mismatch :
    PrefixMismatchDichotomy sx sy

/-- The finite encoding dichotomy is already CLOSED for every source mismatch. -/
noncomputable def encodedSourceMismatch
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    EncodedSourceMismatch M x y W := by
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let cend := sourcePrefixClauseEnd N x tx (W.j + 1)
  let Fx := boundedExecTableauCNF_NTM N x tx
  let Fy := boundedExecTableauCNF_NTM N y ty
  let sx := encodeCNFSpinePrefix (Fx.take cend)
  let sy := encodeCNFSpinePrefix (Fy.take cend)
  refine ⟨sx, sy, ?_⟩
  exact sourceMismatchEncodingDichotomy_closed
    M x y W.j
    W.length_eq W.clock_eq W.head_eq W.prefix_eq
    W.source_diff W.in_radius

/-- Exact new localization problem.
A source-cell mismatch has been proved to alter the encoded source prefix.
What is not yet proved is where that alteration lies relative to the physical
start/end bit offsets of the j-th source cell. -/
def SourceCellMismatchLocalizationGap : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y),
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let bx := sourceCellBitOffset N x tx W.j
    let by := sourceCellBitOffset N y ty W.j
    let ex := sourcePrefixBitEnd N x tx (W.j + 1)
    let ey := sourcePrefixBitEnd N y ty (W.j + 1)
    ∃ q : Nat,
      Nat.min bx by ≤ q ∧
      q < Nat.min ex ey ∧
      let Fx := boundedExecTableauCNF_NTM N x tx
      let Fy := boundedExecTableauCNF_NTM N y ty
      (encodeCircuit (ntmCNFCircuit Fx)).getD q false ≠
        (encodeCircuit (ntmCNFCircuit Fy)).getD q false

/-- Once localization is available, every source mismatch produces a literal
bit whose relation to the shared read cone is decided arithmetically. -/
theorem localizedSourceBit_visibility_split
    (Hloc : SourceCellMismatchLocalizationGap)
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
  rcases Hloc M x y W with ⟨q, hstart, hend, hdiff⟩
  refine ⟨q, hstart, hend, ?_⟩
  exact bitBeforeSharedCone_or_after M x y q

/-- The hidden-source branch is now a concrete lower bound on the candidate's
shared clock.  No semantic endpoint occurs here. -/
def HiddenSourceGrowthObligation : Prop :=
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
      (M.timeBound y.length) <
      q

/-- The final inequality is definitional arithmetic from SharedReadConePrefix. -/
theorem hiddenSourceGrowth_closed :
    HiddenSourceGrowthObligation := by
  intro M x y W q hStart hHidden
  unfold SharedReadConePrefix at hHidden
  omega

#print axioms MCore.Real.PNPDiscovery.bitBeforeSharedCone_or_after
#print axioms MCore.Real.PNPDiscovery.localizedSourceBit_visibility_split
#print axioms MCore.Real.PNPDiscovery.hiddenSourceGrowth_closed

end PNPDiscovery
end Real
end MCore
