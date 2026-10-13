import Mathlib
import ATK.Exact

/-!
# ATK — P vs NP: ponte condicional no formato da ponte NS (`clayC_of_fc`)

* **Alvo exato** (portão ATK): `ATK.Exact.P_ne_NP` — classes P e NP sobre as máquinas `TM2` da
  Mathlib em tempo polinomial (`Turing.TM2ComputableInPolyTime`).
* **Linguagem SAT** sobre `{0,1}`: fórmulas CNF codificadas por pares de bits
  (`00` = incremento unário do índice da variável, `01` = fim de literal positivo,
  `10` = fim de literal negativo, `11` = fim de cláusula).
* **Hipótese H** = `SATInNP ∧ G21PointwiseTM2`, no formato das duas lacunas do programa
  (`m-core-p-vs-np`): P01 (SAT ∈ NP) e G2.1 (todo candidato determinístico polinomial erra SAT
  em alguma entrada), agora enunciadas no modelo da Mathlib e não num modelo interno.
* **Ponte**: `pne_np_of_H : H_PNP → ATK.Exact.P_ne_NP`.

Peças certificadas: `g21_iff_not_inP` — a forma pontual G2.1 (para qualquer linguagem) é
exatamente `¬ InP`; logo a ponte não depende de nenhum modelo interno nem de seleção existencial
de modelo. Força registrada: P01 é teorema clássico (Cook–Levin, parte fácil) cuja máquina `TM2`
ainda não foi construída; G2.1 para SAT é, via Cook–Levin, o próprio P ≠ NP (conteúdo aberto).
-/

namespace ATK.PNPBridge

open Turing

/-! ## SAT -/

/-- Literal: (índice da variável, sinal). -/
abbrev Lit := ℕ × Bool
abbrev Clause := List Lit
abbrev CNF := List Clause

def evalLit (a : ℕ → Bool) (l : Lit) : Bool := if l.2 then a l.1 else !a l.1

def evalCNF (a : ℕ → Bool) (φ : CNF) : Bool := φ.all fun c => c.any (evalLit a)

def Satisfiable (φ : CNF) : Prop := ∃ a : ℕ → Bool, evalCNF a φ = true

def encLit (l : Lit) : List Bool :=
  (List.replicate l.1 [false, false]).flatten ++ (if l.2 then [false, true] else [true, false])

def encClause (c : Clause) : List Bool := (c.map encLit).flatten ++ [true, true]

def encCNF (φ : CNF) : List Bool := (φ.map encClause).flatten

/-- A linguagem SAT: palavras que codificam uma fórmula CNF satisfatível. -/
def SAT : ATK.Exact.Lang := {w | ∃ φ : CNF, encCNF φ = w ∧ Satisfiable φ}

/-- Sanidade 1: a fórmula vazia (verdadeira) está em SAT. -/
theorem nil_mem_SAT : ([] : List Bool) ∈ SAT := by
  show ∃ φ : CNF, encCNF φ = [] ∧ Satisfiable φ
  exact ⟨[], rfl, fun _ => true, rfl⟩

/-- Sanidade 2: a cláusula vazia (falsa) não é satisfatível. -/
theorem emptyClause_unsat : ¬ Satisfiable [[]] := by
  rintro ⟨a, ha⟩
  simp [evalCNF] at ha

/-- Sanidade 3: uma palavra de um bit não codifica fórmula alguma; logo SAT ≠ tudo. -/
theorem single_not_mem_SAT : [true] ∉ SAT := by
  intro hmem
  obtain ⟨φ, hφ, -⟩ := (hmem : ∃ φ : CNF, encCNF φ = [true] ∧ Satisfiable φ)
  have hlen := congrArg List.length hφ
  cases φ with
  | nil => simp [encCNF] at hφ
  | cons c rest =>
    simp only [encCNF, List.map_cons, List.flatten_cons, encClause, List.length_append,
      List.length_cons, List.length_nil] at hlen
    omega

/-! ## G2.1 no modelo da Mathlib -/

open scoped Classical in
/-- O candidato `(M, p)` (máquina `TM2` com alfabetos `Bool`, orçamento polinomial `p`) **erra**
em `w` para a linguagem `L`: não produz `[w ∈ L]` em até `p(|w|)` passos. -/
def FailsAt (M : TM2ComputableAux Bool Bool) (p : Polynomial ℕ) (L : ATK.Exact.Lang)
    (w : List Bool) : Prop :=
  IsEmpty (TM2OutputsInTime M.tm (List.map M.inputAlphabet.invFun w)
    (Option.some ((List.map M.outputAlphabet.invFun) [decide (w ∈ L)])) (p.eval w.length))

/-- **G2.1 pontual** (forma do programa, no modelo da Mathlib): todo candidato determinístico
polinomial erra em alguma entrada. -/
def G21Pointwise (L : ATK.Exact.Lang) : Prop :=
  ∀ (M : TM2ComputableAux Bool Bool) (p : Polynomial ℕ), ∃ w : List Bool, FailsAt M p L w

/-- G2.1 pontual é exatamente `¬ InP` (para qualquer linguagem). -/
theorem g21_iff_not_inP (L : ATK.Exact.Lang) : G21Pointwise L ↔ ¬ ATK.Exact.InP L := by
  unfold ATK.Exact.InP ATK.Exact.InPOn
  constructor
  · rintro h ⟨R⟩
    obtain ⟨w, hw⟩ := h R.toTM2ComputableAux R.time
    exact hw.1 (R.outputsFun w)
  · intro h M p
    by_contra hc
    push_neg at hc
    apply h
    refine ⟨{ toTM2ComputableAux := M, time := p, outputsFun := fun w => ?_ }⟩
    have hw := hc w
    unfold FailsAt at hw
    rw [not_isEmpty_iff] at hw
    exact Classical.choice hw

/-! ## Hipótese H e ponte -/

/-- P01: SAT ∈ NP no modelo da Mathlib. -/
def SATInNP : Prop := ATK.Exact.InNP SAT

/-- **Hipótese H** = P01 ∧ G2.1(SAT). -/
def H_PNP : Prop := SATInNP ∧ G21Pointwise SAT

/-- **Ponte certificada** `H → alvo exato`. -/
theorem pne_np_of_H (h : H_PNP) : ATK.Exact.P_ne_NP := by
  obtain ⟨h1, h2⟩ := h
  unfold ATK.Exact.P_ne_NP
  exact ⟨SAT, h1, (g21_iff_not_inP SAT).mp h2⟩

/-- Forma equivalente de H: `SAT ∈ NP ∧ SAT ∉ P`. -/
theorem H_iff : H_PNP ↔ (ATK.Exact.InNP SAT ∧ ¬ ATK.Exact.InP SAT) := by
  unfold H_PNP SATInNP
  rw [g21_iff_not_inP]

/-- Falsificador de H: um decisor polinomial `TM2` para SAT. -/
theorem H_refuted_by_decider (hP : ATK.Exact.InP SAT) : ¬ H_PNP := by
  rintro ⟨-, h2⟩
  exact (g21_iff_not_inP SAT).mp h2 hP

end ATK.PNPBridge

#print axioms ATK.PNPBridge.nil_mem_SAT
#print axioms ATK.PNPBridge.emptyClause_unsat
#print axioms ATK.PNPBridge.single_not_mem_SAT
#print axioms ATK.PNPBridge.g21_iff_not_inP
#print axioms ATK.PNPBridge.pne_np_of_H
#print axioms ATK.PNPBridge.H_iff
#print axioms ATK.PNPBridge.H_refuted_by_decider
