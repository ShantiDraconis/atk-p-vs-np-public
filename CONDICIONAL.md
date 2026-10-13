# Estado: CONDICIONAL — P vs NP

Auditoria de 13/10/2026 sobre o commit `b75822a` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

A Mathlib não define as classes P e NP, mas define máquinas de Turing e tempo polinomial
(`Turing.TM2ComputableInPolyTime`). O M-Core (`ATK/Exact.lean`, seção `PNP`) define sobre elas
`InP`, `InNP`, `P_eq_NP`, `P_ne_NP` (com `P_ne_NP ↔ ¬ P_eq_NP` provado). No portão ATK só contam
declarações de tipo exatamente `ATK.Exact.P_ne_NP` ou `ATK.Exact.P_eq_NP`.

**Estado no portão: ABERTO.**

## 2. Varredura do conteúdo

2 arquivos Lean · 0 `axiom` · 0 `sorry`/`admit`.

O teorema final importado, `final_external_two_gap_closes`, tem a forma
`FinalExternalTwoGap → ∃ S : OfficialModelSelection, OfficialPneqNP S.model.P S.model.NP`, com
`FinalExternalTwoGap := P01ConstructionGap ∧ G21Pointwise`. É uma **implicação**: a hipótese não
foi demonstrada.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Natureza | Por que é condicional | O que fechar |
|---|---|---|---|---|
| P1 | `P01ConstructionGap` (= `Nonempty P01MachineConstruction`) | **verdadeiro, falta engenharia** | SAT ∈ NP é teorema clássico (parte fácil de Cook–Levin), mas a máquina NTM concreta do modelo interno não foi construída. Pendências declaradas na origem: caso de entrada com índice unário, refinamento global de `evalRun`, verificador integrado | Construir a máquina e provar parada em tempo polinomial e aceitação ⇔ `SATBits` |
| P2 | `G21Pointwise` | **é o problema aberto** | `∀` candidato determinístico polinomial `∃ x` em que ele erra SAT. O próprio repositório prova `G21Pointwise ↔ P02Target` e `G21 ↔ G22` (SAT ∉ P interno). Com Cook–Levin, isso é P ≠ NP: nenhuma reformulação reduz o conteúdo | Uma prova de cota inferior que escape às barreiras conhecidas (relativização, provas naturais, algebrização) |
| P3 | `OfficialModelSelection` / `cookNormalizedExternalContract` (G3) | **fidelidade do modelo** | As definições não estão neste instantâneo. A conclusão é existencial em `S`: se a "seleção oficial" puder ser o próprio modelo interno, a transferência fica trivial e não liga ao enunciado padrão | Trocar `∃ S` por um modelo fixo: provar `InP_interno L ↔ ATK.Exact.InP L` e `InNP_interno L ↔ ATK.Exact.InNP L` (TM2 da Mathlib); então a conclusão vira `ATK.Exact.P_ne_NP` |
| P4 | `PneqNP := ¬ ∀ L, InP L ↔ InNP L` | **sanidade do modelo** | Essa forma só significa P ≠ NP se `InP ⊆ InNP` valer no modelo; senão um modelo defeituoso a tornaria verdadeira por P ⊄ NP. A origem tem `inP_subset_inNP` (`CanonicalPSubsetNP.lean`), ausente deste instantâneo | Incluir `inP_subset_inNP` no conjunto auditado e compilado |
| P5 | Compilação | — | Os 2 arquivos importam módulos `MCore.Real.*` ausentes aqui | CI que compila a partir do commit de origem (`provenance/`) e imprime os axiomas |

## 4. Falsificador exato

P ≠ NP cai ⇔ P = NP: toda linguagem em NP é decidida por uma máquina TM2 em tempo polinomial
(M-Core: `ATK.Closure.pnp_false_iff`). Concretamente, um decisor polinomial para SAT (no modelo
fixado em P3) refuta `G21Pointwise`.

## 5. Condição para mudar o estado

ABERTO → FECHADO somente com uma declaração de tipo `ATK.Exact.P_ne_NP` (ou `P_eq_NP`) aceita
pelo portão, sem `sorry`, só com os axiomas padrão e sem a conclusão (ou um equivalente, como
`G21Pointwise`) entre as hipóteses.

---

**English summary.** Status CONDITIONAL / gate OPEN. The imported final theorem is an implication
from `P01ConstructionGap ∧ G21Pointwise`. P01 (SAT ∈ NP in the internal NTM model) is true but
not yet constructed; `G21Pointwise` is provably equivalent to SAT ∉ P, i.e. it *is* the open
problem. The existential "official model selection" must be replaced by a proven equivalence
with Mathlib-based definitions (P3), and `P ⊆ NP` must be in the audited set (P4).
