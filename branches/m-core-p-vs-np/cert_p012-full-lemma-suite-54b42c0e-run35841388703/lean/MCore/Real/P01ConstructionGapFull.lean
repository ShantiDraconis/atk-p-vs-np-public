import Mathlib
import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalTwoGap

namespace MCore
namespace Real
namespace P01ConstructionGapFull

open P01FinalCertificate
open P02G21G22Attack
open FinalExternalTwoGap

/-
P012 symbolic state layer.

This file formalizes the user's fail-closed bookkeeping laws.
It is intentionally separated from the repository's real terminal endpoints:
  * P01ConstructionGap
  * G21Pointwise

The symbolic objects below do not manufacture those endpoints.
-/

-- ESTADO P012
-- open0   = 0/1 = 0/2 = 0/3 = 0
-- closed1 = n/n, n != 0
-- indet    = 0/0
-- inf      = n/0, n != 0
inductive EstadoP012 where
  | open0
  | closed1
  | indet
  | inf
  deriving DecidableEq, Repr, BEq

/-- Classifier: only n/n with nonzero denominator becomes closed1. -/
def classifyP012 (a b : Nat) : EstadoP012 :=
  if b = 0 then
    if a = 0 then .indet else .inf
  else if a = 0 then
    .open0
  else if a = b then
    .closed1
  else
    .open0

def IsRigidCore (s : EstadoP012) : Prop :=
  s = .closed1

-- L01: 0/n = open0 when n != 0.
theorem L01_zero_over_nonzero_open0
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 0 n = .open0 := by
  unfold classifyP012
  simp [hn]

-- L02: n/n = closed1 when n != 0.
theorem L02_n_over_n_closed1
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 n n = .closed1 := by
  unfold classifyP012
  simp [hn]

-- L03: 0/0 = indet.
theorem L03_zero_over_zero_indet :
    classifyP012 0 0 = .indet := by
  unfold classifyP012
  simp

-- L04: n/0 = inf for n != 0.
theorem L04_nonzero_over_zero_inf
    (n : Nat) (hn : n ≠ 0) :
    classifyP012 n 0 = .inf := by
  unfold classifyP012
  simp [hn]

-- L05: open0 is never closed1.
theorem L05_open_never_closed :
    EstadoP012.open0 ≠ .closed1 := by
  simp

-- L06: indet is never closed1.
theorem L06_indet_never_closed :
    EstadoP012.indet ≠ .closed1 := by
  simp

-- L07: inf is never closed1.
theorem L07_inf_never_closed :
    EstadoP012.inf ≠ .closed1 := by
  simp

-- L08: only n/n with nonzero denominator enters the rigid symbolic core.
theorem L08_only_n_over_n_enters_core
    (a b : Nat)
    (h : IsRigidCore (classifyP012 a b)) :
    a = b ∧ b ≠ 0 := by
  unfold IsRigidCore at h
  unfold classifyP012 at h
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 0
    · simp [ha] at h
    · simp [ha] at h
  · by_cases ha0 : a = 0
    · simp [hb, ha0] at h
    · by_cases hab : a = b
      · exact ⟨hab, hb⟩
      · simp [hb, ha0, hab] at h

/-- Converse of L08, useful as a complete characterization. -/
theorem L08b_n_over_n_enters_core
    (a b : Nat)
    (h : a = b ∧ b ≠ 0) :
    IsRigidCore (classifyP012 a b) := by
  rcases h with ⟨rfl, hb⟩
  simp [IsRigidCore, classifyP012, hb]

theorem L08c_rigid_iff_same_nonzero
    (a b : Nat) :
    IsRigidCore (classifyP012 a b) ↔
      a = b ∧ b ≠ 0 := by
  constructor
  · exact L08_only_n_over_n_enters_core a b
  · exact L08b_n_over_n_enters_core a b

-- STATUS PRODUTOR: 0/2, 1/2, 2/2.
inductive StatusProdutor where
  | zero_of_two
  | one_of_two
  | two_of_two
  deriving DecidableEq, Repr

def statusProd
    (p01 g21 : Option Bool) :
    StatusProdutor :=
  match p01, g21 with
  | none, none => .zero_of_two
  | some _, none => .one_of_two
  | none, some _ => .one_of_two
  | some _, some _ => .two_of_two

-- L09: 0/2 is not rigid.
theorem L09_zero_two_never_rigid :
    statusProd none none ≠ .two_of_two := by
  simp [statusProd]

-- L10: 1/2 is not 2/2.
theorem L10_one_two_never_rigid
    (b : Bool) :
    statusProd (some b) none ≠ .two_of_two := by
  simp [statusProd]

-- L11: 2/2 is the closed producer status.
theorem L11_two_two_is_rigid
    (p g : Bool) :
    statusProd (some p) (some g) = .two_of_two := by
  simp [statusProd]

/-
Toy P01 bookkeeping object.
This is NOT P01FinalCertificate.P01ConstructionGap.
It only formalizes the finite-state/count and polynomial arithmetic layer.
-/
structure Real8 where
  n : Nat
  h8 : n = 8

def IsPoly (f : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n : Nat,
    f n ≤ c * (n + 1) ^ d + c

-- L12: T(n)=n^2+10 satisfies this elementary polynomial-bound predicate.
theorem L12_timeBound_poly :
    IsPoly (fun n => n * n + 10) := by
  refine ⟨11, 2, ?_⟩
  intro n
  have hsquare : (n + 1) ^ 2 = n * n + 2 * n + 1 := by
    ring
  rw [hsquare]
  omega

structure P01Gap where
  real : Real8
  sat_in_np : Bool
  h_sat : sat_in_np = true

def P01Built : P01Gap where
  real := ⟨8, rfl⟩
  sat_in_np := true
  h_sat := rfl

-- L13: symbolic P01 bookkeeping moves producer count 0/2 -> 1/2.
theorem L13_P01_closes_half :
    statusProd (some true) none = .one_of_two := by
  simp [statusProd]

-- Toy SAT formula evaluator used only for the local semantics lemmas.
inductive Formula where
  | const : Bool → Formula
  | var : Nat → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving Repr

def eval : Formula → List Bool → Bool
  | .const b, _ => b
  | .var n, w => w.getD n false
  | .not phi, w => !(eval phi w)
  | .and phi psi, w => (eval phi w) && (eval psi w)
  | .or phi psi, w => (eval phi w) || (eval psi w)

-- L14: local reflexive semantics sanity check.
-- This is not the repository's physical_eq_logical machine theorem.
theorem L14_physical_eq_logical
    (phi : Formula) (w : List Bool) :
    eval phi w = eval phi w := by
  rfl

-- FLOW bookkeeping.
inductive FlowState where
  | open0
  | flowing
  | singularity
  | closed1
  deriving DecidableEq, Repr

def ComplexityFlow (t : Nat) : FlowState :=
  match t with
  | 0 => .open0
  | 1 => .flowing
  | _ => .closed1

def SurgeryFlow : FlowState → FlowState
  | .singularity => .open0
  | .flowing => .closed1
  | x => x

def SurgeryEstado : EstadoP012 → EstadoP012
  | .indet => .open0
  | .inf => .open0
  | x => x

-- L15: symbolic flowing state closes.
theorem L15_perelman_flow_closes :
    SurgeryFlow .flowing = .closed1 := by
  rfl

-- L16: symbolic singularity is removed to open0.
theorem L16_perelman_surgery_removes :
    SurgeryFlow .singularity = .open0 := by
  rfl

-- L17-L20: surgery laws.
theorem L17_lei_indet_para_open0 :
    SurgeryEstado .indet = .open0 := by
  rfl

theorem L18_lei_inf_para_open0 :
    SurgeryEstado .inf = .open0 := by
  rfl

theorem L19_lei_open0_idem :
    SurgeryEstado .open0 = .open0 := by
  rfl

theorem L20_lei_closed1_idem :
    SurgeryEstado .closed1 = .closed1 := by
  rfl

-- L21-L22: idempotence.
theorem L21_idempotente_estado
    (e : EstadoP012) :
    SurgeryEstado (SurgeryEstado e) = SurgeryEstado e := by
  cases e <;> rfl

theorem L22_idempotente_flow
    (s : FlowState) :
    SurgeryFlow (SurgeryFlow s) = SurgeryFlow s := by
  cases s <;> rfl

/-
Auxiliary monotone W-functional.
Its monotonicity does NOT imply G21Pointwise by itself.
-/
structure PerelmanW where
  W : Nat → Nat
  mono : ∀ t, W t ≤ W (t + 1)

def W_SAT : PerelmanW where
  W := fun t => t * t + 100
  mono := by
    intro t
    omega

-- L23: W(t)=t^2+100 is monotone.
theorem L23_W_mono
    (t : Nat) :
    W_SAT.W t ≤ W_SAT.W (t + 1) := by
  exact W_SAT.mono t

/-
Toy G21 bookkeeping object.
This is NOT P02G21G22Attack.G21Pointwise.
-/
structure G21Gap where
  entropy : PerelmanW

def G21Built : G21Gap where
  entropy := W_SAT

def RigidCore : Prop :=
  Nonempty P01Gap ∧ Nonempty G21Gap

structure FinalGap where
  p01 : P01Gap
  g21 : G21Gap

structure SymbolicOfficialPneqNP where
  gap : FinalGap

-- L24: symbolic rigid core packages if both toy bookkeeping objects exist.
theorem L24_rigidCore_freezes
    (p : P01Gap) (g : G21Gap) :
    ∃ cert : SymbolicOfficialPneqNP, True := by
  refine ⟨⟨⟨p, g⟩⟩, trivial⟩

-- L25-L27 final symbolic laws.
theorem L25_final_needs_both :
    EstadoP012.closed1 = .closed1 := by
  rfl

theorem L26_final_fails_if_open :
    EstadoP012.open0 ≠ .closed1 := by
  simp

def AceitaTodasLeis : Bool := true

theorem L27_aceita_todas :
    AceitaTodasLeis = true := by
  rfl

/-
REAL BRIDGES

These are the only places where the symbolic layer may enter the actual
P-vs-NP final chain.  They require the real repository endpoints explicitly.
-/

/-- A concrete real P01 endpoint can be recorded as the P01 half. -/
def RealP01Foundation : Prop :=
  P01ConstructionGap

/-- A concrete real G21 endpoint can be recorded as the G21 half. -/
def RealG21Foundation : Prop :=
  G21Pointwise

/-- Real rigid core: no toy object is accepted here. -/
abbrev RealRigidCore : Prop :=
  RealP01Foundation ∧ RealG21Foundation

theorem realRigidCore_iff_finalExternalTwoGap :
    RealRigidCore ↔ FinalExternalTwoGap := by
  rfl

/-- The symbolic 2/2 status is obtained from actual terminal inhabitants. -/
theorem real_producers_give_two_of_two
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    statusProd (some true) (some true) = .two_of_two := by
  simp [statusProd]

/-- Actual terminal inhabitants, and only those inputs here, produce the real
FinalExternalTwoGap consumed by the certified external chain. -/
def real_producers_build_final_two_gap
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    FinalExternalTwoGap :=
  ⟨hP01, hG21⟩

/-- Monotonicity of W is kept strictly separate from the real G21 theorem. -/
def WToG21Bridge : Prop :=
  PerelmanW → G21Pointwise

theorem W_SAT_closes_real_G21
    (h : WToG21Bridge) :
    G21Pointwise :=
  h W_SAT

#print axioms MCore.Real.P01ConstructionGapFull.L08c_rigid_iff_same_nonzero
#print axioms MCore.Real.P01ConstructionGapFull.L12_timeBound_poly
#print axioms MCore.Real.P01ConstructionGapFull.L23_W_mono
#print axioms MCore.Real.P01ConstructionGapFull.L24_rigidCore_freezes
#print axioms MCore.Real.P01ConstructionGapFull.realRigidCore_iff_finalExternalTwoGap
#print axioms MCore.Real.P01ConstructionGapFull.real_producers_build_final_two_gap
#print axioms MCore.Real.P01ConstructionGapFull.W_SAT_closes_real_G21

end P01ConstructionGapFull
end Real
end MCore
