import MCore.Real.PNPDiscovery.AlphaRenameCore
import MCore.Real.PNPDiscovery.LayoutLeakage

namespace MCore
namespace Real
namespace PNPDiscovery

open PNPNTMTableauEncoding

def renameLiteral (ρ : Nat → Nat) (l : NTMLiteral) : NTMLiteral :=
  ⟨ρ l.var, l.positive⟩

def renameClause (ρ : Nat → Nat) (c : NTMClause) : NTMClause :=
  c.map (renameLiteral ρ)

def renameCNF (ρ : Nat → Nat) (F : NTMCNF) : NTMCNF :=
  F.map (renameClause ρ)

theorem renameLiteral_litFor
    (ρ : Nat → Nat)
    (v : Nat)
    (b : Bool) :
    renameLiteral ρ (ntmLitFor v b) =
      ntmLitFor (ρ v) b := by
  cases b <;> rfl

theorem renameClause_singleton_litFor
    (ρ : Nat → Nat)
    (v : Nat)
    (b : Bool) :
    renameClause ρ [ntmLitFor v b] =
      [ntmLitFor (ρ v) b] := by
  simp [renameClause, renameLiteral_litFor]

/-- Alpha-equivalence allows each CNF to be injectively renamed into one
common variable namespace. -/
def CNFAlphaEquivalent
    (F G : NTMCNF) : Prop :=
  ∃ ρ σ : Nat → Nat,
    Function.Injective ρ ∧
    Function.Injective σ ∧
    renameCNF ρ F = renameCNF σ G

theorem CNFAlphaEquivalent_refl
    (F : NTMCNF) :
    CNFAlphaEquivalent F F := by
  refine ⟨id, id, Function.injective_id, Function.injective_id, ?_⟩
  simp [renameCNF, renameClause, renameLiteral]

/-- Translation on Nat is injective. -/
theorem addRight_injective
    (k : Nat) :
    Function.Injective (fun n => n + k) := by
  intro a b h
  omega

/-- A three-symbol block depends logically only on target polarity pattern;
changing a consecutive variable base is alpha-renaming only. -/
theorem symbolBlock_alphaEquivalent_of_bases
    (B C : Nat)
    (target : Option Bool) :
    CNFAlphaEquivalent
      (ntmSetSymbolClauses []
        (symbolVarsFromBase B) target)
      (ntmSetSymbolClauses []
        (symbolVarsFromBase C) target) := by
  refine ⟨
    (fun n => n + C),
    (fun n => n + B),
    addRight_injective C,
    addRight_injective B,
    ?_⟩
  cases target with
  | none =>
      simp [renameCNF, renameClause, renameLiteral,
        ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
        symbolVarsFromBase, ntmSymbolCode]
      omega
  | some b =>
      cases b <;>
        simp [renameCNF, renameClause, renameLiteral,
          ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
          symbolVarsFromBase, ntmSymbolCode] <;>
        omega

/-- Different-clock head blocks are syntactically different but alpha-equivalent
whenever their represented source symbol is the same. -/
theorem headBlocks_alphaEquivalent
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hTarget :
      sourceHeadSymbol x = sourceHeadSymbol y) :
    CNFAlphaEquivalent
      (initialHeadBlock M x t)
      (initialHeadBlock M y u) := by
  unfold initialHeadBlock
  rw [hTarget]
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
  rw [hv, hw]
  exact symbolBlock_alphaEquivalent_of_bases
    (ntmHeadBase M t)
    (ntmHeadBase M u)
    (sourceHeadSymbol y)

/-- Same for the first canonical left cell: layout-length leakage is purely
a renaming of its three variable IDs. -/
theorem firstLeftBlocks_alphaEquivalent
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat) :
    CNFAlphaEquivalent
      (ntmSetLeftCell [] M x t 0 0 M.machine.blank)
      (ntmSetLeftCell [] M y u 0 0 M.machine.blank) := by
  unfold ntmSetLeftCell
  have hv :
      ntmLeftVar M x t 0 0 =
        symbolVarsFromBase (ntmLeftBase M x t) := by
    funext a
    simp [ntmLeftVar, symbolVarsFromBase]
  have hw :
      ntmLeftVar M y u 0 0 =
        symbolVarsFromBase (ntmLeftBase M y u) := by
    funext a
    simp [ntmLeftVar, symbolVarsFromBase]
  rw [hv, hw]
  exact symbolBlock_alphaEquivalent_of_bases
    (ntmLeftBase M x t)
    (ntmLeftBase M y u)
    M.machine.blank

#print axioms MCore.Real.PNPDiscovery.symbolBlock_alphaEquivalent_of_bases
#print axioms MCore.Real.PNPDiscovery.headBlocks_alphaEquivalent
#print axioms MCore.Real.PNPDiscovery.firstLeftBlocks_alphaEquivalent

end PNPDiscovery
end Real
end MCore
