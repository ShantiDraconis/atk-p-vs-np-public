import MCore.Real.PNPDiscovery.ArithmeticRouteFalsification
import MCore.Real.PNPDiscovery.SymbolBlockLocalization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P02ComplementRunRealization

/-- Canonical consecutive variable family starting at base B. -/
def symbolVarsFromBase (B : Nat) : Option Bool → Nat :=
  fun a => B + ntmSymbolCode a

/-- Equal encoded symbol blocks with the same target force equality of the
underlying three-clause CNF blocks. -/
theorem encodedSymbolBlock_eq_implies_clause_eq
    (v w : Option Bool → Nat)
    (target : Option Bool)
    (h :
      encodedSymbolBlock v target =
        encodedSymbolBlock w target) :
    ntmSetSymbolClauses [] v target =
      ntmSetSymbolClauses [] w target := by
  by_contra hne
  exact
    (unequal_clausePrefixes_give_unequal_spines
      (ntmSetSymbolClauses [] v target)
      (ntmSetSymbolClauses [] w target)
      hne) h

/-- For consecutive variable families, one encoded symbol block determines
its base exactly. -/
theorem encodedSymbolBlock_base_injective
    (target : Option Bool) :
    Function.Injective
      (fun B : Nat =>
        encodedSymbolBlock
          (symbolVarsFromBase B)
          target) := by
  intro B C h
  have hc :=
    encodedSymbolBlock_eq_implies_clause_eq
      (symbolVarsFromBase B)
      (symbolVarsFromBase C)
      target h
  cases target with
  | none =>
      simp [symbolVarsFromBase, ntmSetSymbolClauses,
        ntmAlphabet, ntmLitFor, ntmPos, ntmNeg,
        ntmSymbolCode] at hc
      omega
  | some b =>
      cases b <;>
        simp [symbolVarsFromBase, ntmSetSymbolClauses,
          ntmAlphabet, ntmLitFor, ntmPos, ntmNeg,
          ntmSymbolCode] at hc <;>
        omega

/-- Head base is injective in the declared tableau clock because stateCount+1
is strictly positive. -/
theorem ntmHeadBase_injective_time
    (M : PolyNTMCandidate) :
    Function.Injective (ntmHeadBase M) := by
  intro t u h
  unfold ntmHeadBase ntmStateSlots at h
  have hQ : 0 < ntmStateCount M := by
    simp [ntmStateCount]
  nlinarith

/-- Different clocks force different encoded time-zero head blocks even when
the source-head symbol itself is the same. -/
theorem headBlock_diff_of_clock_diff
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hTarget :
      sourceHeadSymbol x = sourceHeadSymbol y)
    (hClock : t ≠ u) :
    encodeCNFSpinePrefix (initialHeadBlock M x t) ≠
      encodeCNFSpinePrefix (initialHeadBlock M y u) := by
  intro hEq
  unfold initialHeadBlock at hEq
  have hv :
      ntmHeadVar M t 0 =
        symbolVarsFromBase (ntmHeadBase M t) := by
    funext a
    simp [ntmHeadVar, symbolVarsFromBase]
  have hw :
      ntmHeadVar M u 0 =
        symbolVarsFromBase (ntmHeadBase M u) := by
    funext a
    simp [ntmHeadVar, symbolVarsFromBase]
  rw [hTarget] at hEq
  change
    encodedSymbolBlock (ntmHeadVar M t 0)
        (sourceHeadSymbol y) =
      encodedSymbolBlock (ntmHeadVar M u 0)
        (sourceHeadSymbol y) at hEq
  rw [hv, hw] at hEq
  have hBase :=
    encodedSymbolBlock_base_injective
      (sourceHeadSymbol y) hEq
  exact hClock (ntmHeadBase_injective_time M hBase)

/-- Left base is strictly increasing in retained radius at fixed clock. -/
theorem ntmLeftBase_injective_length_at_fixed_clock
    (M : PolyNTMCandidate)
    (t : Nat)
    {x y : BitString}
    (h :
      ntmLeftBase M x t =
        ntmLeftBase M y t) :
    x.length = y.length := by
  unfold ntmLeftBase ntmHeadBase ntmStateSlots ntmRadius at h
  omega

/-- With equal clock but unequal source length, the encoded first left-cell
block already differs.  The canonical left target is blank on both inputs. -/
theorem firstLeftBlock_diff_of_length_diff
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat)
    (hLen : x.length ≠ y.length) :
    encodeCNFSpinePrefix
        (ntmSetLeftCell [] M x t 0 0 M.machine.blank) ≠
      encodeCNFSpinePrefix
        (ntmSetLeftCell [] M y t 0 0 M.machine.blank) := by
  intro hEq
  unfold ntmSetLeftCell at hEq
  have hvx :
      ntmLeftVar M x t 0 0 =
        symbolVarsFromBase (ntmLeftBase M x t) := by
    funext a
    simp [ntmLeftVar, symbolVarsFromBase]
  have hvy :
      ntmLeftVar M y t 0 0 =
        symbolVarsFromBase (ntmLeftBase M y t) := by
    funext a
    simp [ntmLeftVar, symbolVarsFromBase]
  change
    encodedSymbolBlock (ntmLeftVar M x t 0 0)
        M.machine.blank =
      encodedSymbolBlock (ntmLeftVar M y t 0 0)
        M.machine.blank at hEq
  rw [hvx, hvy] at hEq
  have hBase :=
    encodedSymbolBlock_base_injective
      M.machine.blank hEq
  exact hLen
    (ntmLeftBase_injective_length_at_fixed_clock M t hBase)

/-- Exact layout-leak dichotomy for unequal-length inputs. -/
theorem unequalLength_layoutLeak
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length ≠ y.length) :
    M.timeBound x.length ≠ M.timeBound y.length ∨
      (M.timeBound x.length = M.timeBound y.length ∧
        encodeCNFSpinePrefix
            (ntmSetLeftCell []
              (complementToNTMCandidate M)
              x (M.timeBound x.length) 0 0
              (complementToNTMCandidate M).machine.blank) ≠
          encodeCNFSpinePrefix
            (ntmSetLeftCell []
              (complementToNTMCandidate M)
              y (M.timeBound y.length) 0 0
              (complementToNTMCandidate M).machine.blank)) := by
  by_cases hClock :
      M.timeBound x.length = M.timeBound y.length
  · right
    refine ⟨hClock, ?_⟩
    rw [← hClock]
    exact firstLeftBlock_diff_of_length_diff
      (complementToNTMCandidate M)
      x y (M.timeBound x.length) hLen
  · exact Or.inl hClock

#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_base_injective
#print axioms MCore.Real.PNPDiscovery.ntmHeadBase_injective_time
#print axioms MCore.Real.PNPDiscovery.headBlock_diff_of_clock_diff
#print axioms MCore.Real.PNPDiscovery.firstLeftBlock_diff_of_length_diff
#print axioms MCore.Real.PNPDiscovery.unequalLength_layoutLeak

end PNPDiscovery
end Real
end MCore
