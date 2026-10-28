import Mathlib

/-!
# ATK — P ≠ NP: implicações lógicas (nível de conjuntos)

Classes modeladas abstratamente como conjuntos de linguagens; NÃO há aqui máquinas de Turing,
tempo polinomial nem SAT formalizados. Os enunciados registram apenas a forma lógica:

* `p_ne_np_of_np_not_subset_ppoly` — P ⊆ P/poly e NP ⊄ P/poly ⇒ P ≠ NP.
* `p_ne_np_of_sat`                 — SAT ∈ NP e SAT ∉ P ⇒ P ≠ NP.

As premissas (NP ⊄ P/poly, SAT ∉ P) são exatamente o problema em aberto.
-/

namespace ATK.PvsNP

theorem p_ne_np_of_np_not_subset_ppoly {Lang : Type*} (P NP Ppoly : Set Lang)
    (hP : P ⊆ Ppoly) (hNP : ¬ NP ⊆ Ppoly) : P ≠ NP := by
  intro h
  rw [h] at hP
  exact hNP hP

theorem p_ne_np_of_sat {Lang : Type*} (P NP : Set Lang) (SAT : Lang)
    (hSAT : SAT ∈ NP) (hnot : SAT ∉ P) : P ≠ NP := by
  intro h
  rw [h] at hnot
  exact hnot hSAT

end ATK.PvsNP

#print axioms ATK.PvsNP.p_ne_np_of_np_not_subset_ppoly
#print axioms ATK.PvsNP.p_ne_np_of_sat
