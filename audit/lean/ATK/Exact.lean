import Mathlib
import ATK.BealDescent

/-!
# ATK — alvos EXATOS (enunciados oficiais), sem `Prop` livre

Este módulo substitui os campos `Target : Prop` arbitrários dos portões (`Lane`, `TerminalGate`,
`ProofCertificate`, `Producer`) pelos enunciados oficiais, escritos com objetos da Mathlib:

* **RH** — `RiemannHypothesis` da Mathlib (zeros não triviais de `riemannZeta` na reta crítica).
* **Navier–Stokes** — os quatro enunciados (A), (B), (C), (D) do texto oficial de Fefferman
  (Clay Institute), em ℝ³ com derivadas parciais, divergência, Laplaciano, gradiente de pressão,
  suavidade C^∞ em ℝ³ × [0, ∞), decaimento rápido e energia limitada (integral de Lebesgue).
* **Beal** — `ATK.BealDescent.BealStatement` (aritmética de ℕ).
* **P ≠ NP** — classes P e NP definidas com as máquinas de Turing `TM2` da Mathlib em tempo
  polinomial; NP via verificadores com certificado de tamanho polinomial.

Os testes de sanidade abaixo verificam que as definições têm conteúdo (não são vazias nem
triviais): o campo zero resolve NS; o campo identidade NÃO resolve (divergência 3); Beal implica
Fermat; Beal com expoente 2 é falso; P ≠ NP é exatamente ¬(P = NP); P contém um problema concreto.

**BSD, Yang–Mills e Hodge não são enunciáveis exatamente na Mathlib v4.34.1**: faltam a função L
de uma curva elíptica com continuação analítica (BSD), a teoria quântica de campos de Yang–Mills
em ℝ⁴ com axiomas de Wightman/Osterwalder–Schrader (YM), e a cohomologia de Hodge de variedades
projetivas complexas com ciclos algébricos e mapa de classe (Hodge). Definições falsas para elas
seriam piores que nenhuma; o que falta está listado em `ATK_AGENDA.md`.

Nenhuma conjectura é provada aqui. Nenhum `axiom` é introduzido.
-/

noncomputable section

namespace ATK.Exact

open MeasureTheory Set
open scoped ContDiff

/-! ## Riemann -/

/-- RH exatamente como na Mathlib. -/
abbrev RH : Prop := RiemannHypothesis

/-- Desdobramento literal: todo zero de ζ que não é trivial (−2, −4, …) nem o polo tem parte real 1/2. -/
theorem RH_iff : RH ↔ ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    s.re = 1 / 2 :=
  Iff.rfl

/-! ## Navier–Stokes (enunciado oficial, Fefferman / Clay Institute) -/

/-- ℝ³ euclidiano. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Vetor `eᵢ` da base canônica. -/
abbrev e (i : Fin 3) : R3 := EuclideanSpace.single i 1

/-- Derivada parcial `∂ᵢ f`. -/
def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) (f : R3 → F) : R3 → F :=
  fun x => fderiv ℝ f x (e i)

/-- Divergência `∇·v = Σᵢ ∂ᵢ vᵢ`. -/
def div3 (v : R3 → R3) (x : R3) : ℝ := ∑ i, pd i (fun y => v y i) x

/-- Laplaciano `Δv = Σᵢ ∂ᵢ∂ᵢ v`. -/
def lap3 (v : R3 → R3) (x : R3) : R3 := ∑ i, pd i (pd i v) x

/-- Gradiente `∇q = Σᵢ (∂ᵢ q) eᵢ`. -/
def grad3 (q : R3 → ℝ) (x : R3) : R3 := ∑ i, pd i q x • e i

/-- Termo convectivo `(v·∇)v = Σⱼ vⱼ ∂ⱼ v`. -/
def conv3 (v : R3 → R3) (x : R3) : R3 := ∑ j, v x j • pd j v x

/-- (1) momento, (2) incompressibilidade, (3) dado inicial e (6) suavidade em ℝ³ × [0, ∞).
`u t x` é a velocidade e `p t x` a pressão no instante `t` e ponto `x`. -/
structure NSClassical (ν : ℝ) (u0 : R3 → R3) (f : ℝ → R3 → R3) (u : ℝ → R3 → R3)
    (p : ℝ → R3 → ℝ) : Prop where
  smooth_u : ContDiffOn ℝ ∞ (fun z : ℝ × R3 => u z.1 z.2) (Ici 0 ×ˢ univ)
  smooth_p : ContDiffOn ℝ ∞ (fun z : ℝ × R3 => p z.1 z.2) (Ici 0 ×ˢ univ)
  momentum : ∀ t, 0 ≤ t → ∀ x, derivWithin (fun s => u s x) (Ici 0) t + conv3 (u t) x =
    ν • lap3 (u t) x - grad3 (p t) x + f t x
  incompressible : ∀ t, 0 ≤ t → ∀ x, div3 (u t) x = 0
  initial : ∀ x, u 0 x = u0 x

/-- (7) energia limitada: `∫ |u(x,t)|² dx ≤ C` para todo `t ≥ 0` (integral de Lebesgue, que vale
`∞` quando a função não é integrável — não há o atalho "integral de não integrável = 0"). -/
def BoundedEnergy (u : ℝ → R3 → R3) : Prop :=
  ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C

/-- (10) periodicidade espacial de `u` e `p`. -/
def SpacePeriodic (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ x (j : Fin 3), u t (x + e j) = u t x ∧ p t (x + e j) = p t x

/-- (4) decaimento rápido do dado: `(1 + |x|)^K ‖Dᵏu⁰(x)‖ ≤ C_{k,K}` para todos `k, K`. -/
def RapidDecay (u0 : R3 → R3) : Prop :=
  ∀ k K : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ k u0 x‖ ≤ C

/-- (5) decaimento da força em `(x, t)`. -/
def ForceDecay (f : ℝ → R3 → R3) : Prop :=
  ∀ k K : ℕ, ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ x, (1 + ‖x‖ + t) ^ K *
    ‖iteratedFDerivWithin ℝ k (fun z : ℝ × R3 => f z.1 z.2) (Ici 0 ×ˢ univ) (t, x)‖ ≤ C

/-- (8) dado periódico. -/
def PeriodicData (u0 : R3 → R3) : Prop :=
  ∀ x (j : Fin 3), u0 (x + e j) = u0 x

/-- (9) força periódica em `x` com decaimento em `t`. -/
def PeriodicForce (f : ℝ → R3 → R3) : Prop :=
  (∀ t x (j : Fin 3), f t (x + e j) = f t x) ∧
  ∀ k K : ℕ, ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ x, (1 + t) ^ K *
    ‖iteratedFDerivWithin ℝ k (fun z : ℝ × R3 => f z.1 z.2) (Ici 0 ×ˢ univ) (t, x)‖ ≤ C

/-- Força suave em ℝ³ × [0, ∞). -/
def SmoothForce (f : ℝ → R3 → R3) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × R3 => f z.1 z.2) (Ici 0 ×ˢ univ)

/-- (A) Existência e suavidade em ℝ³. -/
def ClayA : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u0 : R3 → R3, ContDiff ℝ ∞ u0 → (∀ x, div3 u0 x = 0) → RapidDecay u0 →
    ∃ u p, NSClassical ν u0 (fun _ _ => 0) u p ∧ BoundedEnergy u

/-- (B) Existência e suavidade em ℝ³/ℤ³. -/
def ClayB : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u0 : R3 → R3, ContDiff ℝ ∞ u0 → (∀ x, div3 u0 x = 0) → PeriodicData u0 →
    ∃ u p, NSClassical ν u0 (fun _ _ => 0) u p ∧ SpacePeriodic u p

/-- (C) Explosão em ℝ³ (para `ν` dado; por mudança de escala todos os `ν > 0` são equivalentes). -/
def ClayC : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ (u0 : R3 → R3) (f : ℝ → R3 → R3),
    ContDiff ℝ ∞ u0 ∧ (∀ x, div3 u0 x = 0) ∧ RapidDecay u0 ∧ SmoothForce f ∧ ForceDecay f ∧
    ¬ ∃ u p, NSClassical ν u0 f u p ∧ BoundedEnergy u

/-- (D) Explosão em ℝ³/ℤ³. -/
def ClayD : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ (u0 : R3 → R3) (f : ℝ → R3 → R3),
    ContDiff ℝ ∞ u0 ∧ (∀ x, div3 u0 x = 0) ∧ PeriodicData u0 ∧ SmoothForce f ∧ PeriodicForce f ∧
    ¬ ∃ u p, NSClassical ν u0 f u p ∧ SpacePeriodic u p

/-- O problema do milênio de Navier–Stokes: provar (A), (B), (C) ou (D). -/
def NavierStokes : Prop := ClayA ∨ ClayB ∨ ClayC ∨ ClayD

/-! ### Sanidade das definições de Navier–Stokes -/

/-- `∂ᵢ (y ↦ yⱼ) = δᵢⱼ`: o operador `pd` é a derivada parcial de verdade. -/
theorem pd_coord (i j : Fin 3) (x : R3) :
    pd i (fun y : R3 => y j) x = if j = i then 1 else 0 := by
  have hd : HasFDerivAt (fun y : R3 => y j) (EuclideanSpace.proj j : R3 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt
  show fderiv ℝ (fun y : R3 => y j) x (e i) = _
  rw [hd.fderiv]
  simp [e]

/-- A divergência do campo identidade é 3. -/
theorem div3_id (x : R3) : div3 (fun y => y) x = 3 := by
  simp [div3, pd_coord]
  try norm_num

/-- O campo `u(t, x) = x` NÃO é solução (viola a incompressibilidade): as equações têm conteúdo. -/
theorem identity_field_not_solution (ν : ℝ) (u0 : R3 → R3) (f : ℝ → R3 → R3)
    (p : ℝ → R3 → ℝ) : ¬ NSClassical ν u0 f (fun _ y => y) p := by
  intro h
  have h0 := h.incompressible 0 le_rfl 0
  norm_num [div3_id] at h0

/-- `∂ᵢ` de uma função nula é nula. -/
theorem pd_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) :
    pd i (fun _ : R3 => (0 : F)) = fun _ => 0 := by
  funext x
  simp [pd]

theorem conv3_zero (x : R3) : conv3 (fun _ => 0) x = 0 := by
  simp [conv3, pd_zero, PiLp.zero_apply]

theorem lap3_zero (x : R3) : lap3 (fun _ => 0) x = 0 := by
  simp [lap3, pd_zero]

theorem grad3_zero (x : R3) : grad3 (fun _ => 0) x = 0 := by
  simp [grad3, pd_zero]

theorem div3_zero (x : R3) : div3 (fun _ => 0) x = 0 := by
  simp [div3, pd, PiLp.zero_apply]

/-- O campo nulo é solução com dado nulo, energia limitada e periodicidade: as condições são
satisfazíveis (a definição não é vazia por engano). -/
theorem zero_solution (ν : ℝ) :
    NSClassical ν (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
    BoundedEnergy (fun _ _ => 0) ∧ SpacePeriodic (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨⟨contDiffOn_const, contDiffOn_const, ?_, ?_, fun _ => rfl⟩, ⟨0, fun t _ => ?_⟩,
    fun t _ x j => ⟨rfl, rfl⟩⟩
  · intro t _ x
    have hd : derivWithin (fun _ : ℝ => (0 : R3)) (Ici 0) t = 0 := by
      rw [derivWithin_fun_const]
      rfl
    show derivWithin (fun _ : ℝ => (0 : R3)) (Ici 0) t + conv3 (fun _ => 0) x =
      ν • lap3 (fun _ => 0) x - grad3 (fun _ => 0) x + 0
    rw [hd, conv3_zero, lap3_zero, grad3_zero]
    simp
  · intro t _ x
    exact div3_zero x
  · show ∫⁻ x : R3, ‖(0 : R3)‖ₑ ^ 2 ≤ ENNReal.ofReal 0
    simp

/-- O dado nulo é admissível para (A) e (B). -/
theorem zero_data_admissible :
    ContDiff ℝ ∞ (fun _ : R3 => (0 : R3)) ∧ (∀ x, div3 (fun _ => 0) x = 0) ∧
    RapidDecay (fun _ => 0) ∧ PeriodicData (fun _ => 0) := by
  refine ⟨contDiff_const, fun x => div3_zero x, fun k K => ⟨0, fun x => ?_⟩,
    fun x j => rfl⟩
  cases k with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ k => simp [iteratedFDeriv_succ_const]

/-! ## Beal -/

/-- Beal exatamente: `Aˣ + Bʸ = Cᶻ`, `A, B, C > 0`, `x, y, z > 2` ⇒ fator primo comum (gcd > 1). -/
abbrev Beal : Prop := ATK.BealDescent.BealStatement

/-- Instância: 2³ + 2³ = 2⁴ tem fator comum 2. -/
theorem beal_instance : 2 ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ 1 < Nat.gcd 2 (Nat.gcd 2 2) := by
  norm_num

/-- A hipótese `> 2` nos expoentes é essencial: com expoente 2, 3² + 4² = 5² não tem fator comum. -/
theorem beal_needs_exponents_gt_two :
    ¬ ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 1 < x → 1 < y → 1 < z →
      A ^ x + B ^ y = C ^ z → 1 < Nat.gcd A (Nat.gcd B C) := by
  intro h
  have h0 := h 3 4 5 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h0

/-- Ponte real: Beal implica o Último Teorema de Fermat (enunciado da Mathlib). -/
theorem flt_of_beal (h : Beal) : FermatLastTheorem := by
  intro n hn
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd heq
  have h1 := h a b c n n n (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
    (Nat.pos_of_ne_zero hc) (by omega) (by omega) (by omega) heq
  have h2 : ({a, b, c} : Finset ℕ).gcd id = Nat.gcd a (Nat.gcd b c) := by
    simp only [Finset.gcd_insert, Finset.gcd_singleton, id_eq, normalize_eq]
    try rfl
  omega

/-! ## P ≠ NP (máquinas de Turing `TM2` da Mathlib) -/

section PNP

open Turing Computability

/-- Linguagens sobre o alfabeto {0, 1}. -/
abbrev Lang : Type := Set (List Bool)

/-- Codificação de (palavra, certificado) — é `(encodingProd (encodingList Bool) (encodingList Bool)).encode`. -/
def pairEnc (wc : List Bool × List Bool) : List (Bool ⊕ Bool) :=
  wc.1.map Sum.inl ++ wc.2.map Sum.inr

open scoped Classical in
/-- Problema de decisão `L ⊆ α` (com codificação `ea`) resolvido por uma máquina de Turing em
tempo polinomial no tamanho da entrada: a máquina devolve `[true]` ou `[false]`. -/
def InPOn {α Γ : Type} (ea : α → List Γ) (L : Set α) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea (fun b : Bool => [b]) (fun a => decide (a ∈ L)))

/-- Classe P. -/
def InP (L : Lang) : Prop := InPOn (id : List Bool → List Bool) L

/-- Classe NP: verificador em P e certificados de tamanho polinomial. -/
def InNP (L : Lang) : Prop :=
  ∃ (V : Set (List Bool × List Bool)) (q : Polynomial ℕ), InPOn pairEnc V ∧
    ∀ w, w ∈ L ↔ ∃ c : List Bool, c.length ≤ q.eval w.length ∧ (w, c) ∈ V

/-- P = NP. -/
def P_eq_NP : Prop := ∀ L : Lang, InNP L → InP L

/-- P ≠ NP. -/
def P_ne_NP : Prop := ∃ L : Lang, InNP L ∧ ¬ InP L

/-- P ≠ NP é exatamente a negação de P = NP. -/
theorem P_ne_NP_iff : P_ne_NP ↔ ¬ P_eq_NP :=
  ⟨fun ⟨L, h1, h2⟩ h => h2 (h L h1), fun h => by
    by_contra hc
    exact h (fun L hL => by
      by_contra hp
      exact hc ⟨L, hL, hp⟩)⟩

/-- A noção de tempo polinomial é satisfazível: o problema "o bit é 1?" está em P. -/
theorem inP_bit_example : InPOn (fun b : Bool => [b]) ({true} : Set Bool) := by
  have h : (fun a : Bool => @decide (a ∈ ({true} : Set Bool)) (Classical.propDecidable _)) = id := by
    funext b
    cases b <;> simp
  unfold InPOn
  rw [h]
  exact ⟨idComputableInPolyTime _⟩

end PNP

/-! ## Certificado terminal exato (sem `Prop` livre) -/

/-- O que um fechamento das quatro linhas enunciáveis teria de entregar: os enunciados oficiais.
Nenhum termo deste tipo é construído aqui. -/
structure ExactCertificate : Prop where
  rh : RiemannHypothesis
  navierStokes : NavierStokes
  beal : Beal
  pNeNP : P_ne_NP

end ATK.Exact

end

#print axioms ATK.Exact.RH_iff
#print axioms ATK.Exact.pd_coord
#print axioms ATK.Exact.div3_id
#print axioms ATK.Exact.identity_field_not_solution
#print axioms ATK.Exact.pd_zero
#print axioms ATK.Exact.conv3_zero
#print axioms ATK.Exact.lap3_zero
#print axioms ATK.Exact.grad3_zero
#print axioms ATK.Exact.div3_zero
#print axioms ATK.Exact.zero_solution
#print axioms ATK.Exact.zero_data_admissible
#print axioms ATK.Exact.beal_instance
#print axioms ATK.Exact.beal_needs_exponents_gt_two
#print axioms ATK.Exact.flt_of_beal
#print axioms ATK.Exact.P_ne_NP_iff
#print axioms ATK.Exact.inP_bit_example
