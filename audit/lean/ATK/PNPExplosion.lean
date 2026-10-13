import Mathlib
import ATK.Exact
import ATK.PNPBridge

/-!
# ATK — Linha de explosão para P vs NP

Adaptação da linha de explosão do NS. Aqui há duas explosões possíveis, uma para cada lado:

* **explosão de cota inferior** (lado P ≠ NP): `G21Pointwise SAT` — TODO candidato
  determinístico com orçamento polinomial erra SAT em alguma entrada; o custo de decidir SAT
  "explode" além de qualquer polinômio;
* **explosão de colapso** (lado P = NP): `CollapseWitness` — um decisor `TM2` polinomial para SAT.
  Refuta H (`collapse_refutes_H`); com a redução de Cook–Levin (clássica, não formalizada em
  `TM2`) daria `P_eq_NP`.

Certificado: as duas explosões são exatamente complementares (`lowerBound_iff_no_collapse`,
`explosion_dichotomy`), e o alvo é exatamente a negação do colapso total
(`ATK.Exact.P_ne_NP_iff`). Nenhuma das duas é conhecida.
-/

namespace ATK.PNPExplosion

open ATK.PNPBridge

/-- Explosão de colapso: SAT tem decisor `TM2` polinomial. -/
def CollapseWitness : Prop := ATK.Exact.InP SAT

/-- Explosão de cota inferior: todo candidato polinomial erra SAT em alguma entrada. -/
def LowerBoundExplosion : Prop := G21Pointwise SAT

theorem lowerBound_iff_no_collapse : LowerBoundExplosion ↔ ¬ CollapseWitness :=
  g21_iff_not_inP SAT

/-- Exatamente uma das duas explosões acontece. -/
theorem explosion_dichotomy : (CollapseWitness ∨ LowerBoundExplosion) ∧
    ¬ (CollapseWitness ∧ LowerBoundExplosion) := by
  constructor
  · by_cases h : CollapseWitness
    · exact Or.inl h
    · exact Or.inr (lowerBound_iff_no_collapse.mpr h)
  · rintro ⟨hc, hl⟩
    exact lowerBound_iff_no_collapse.mp hl hc

/-- O colapso refuta a hipótese H da ponte. -/
theorem collapse_refutes_H (hc : CollapseWitness) : ¬ H_PNP :=
  H_refuted_by_decider hc

/-- A explosão de cota inferior, com SAT ∈ NP, fecha o alvo exato. -/
theorem lowerBound_closes (hnp : SATInNP) (hl : LowerBoundExplosion) : ATK.Exact.P_ne_NP :=
  pne_np_of_H ⟨hnp, hl⟩

/-- O alvo é exatamente a negação do colapso total `P = NP`. -/
theorem target_iff_no_total_collapse : ATK.Exact.P_ne_NP ↔ ¬ ATK.Exact.P_eq_NP :=
  ATK.Exact.P_ne_NP_iff

end ATK.PNPExplosion

#print axioms ATK.PNPExplosion.lowerBound_iff_no_collapse
#print axioms ATK.PNPExplosion.explosion_dichotomy
#print axioms ATK.PNPExplosion.collapse_refutes_H
#print axioms ATK.PNPExplosion.lowerBound_closes
#print axioms ATK.PNPExplosion.target_iff_no_total_collapse
