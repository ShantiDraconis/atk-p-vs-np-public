/- ATK BATCH02 — full source archive, not compiled; unique blobs in this batch. -/

/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/MCore/A4Scale.lean blob ca603ba7a9530fcec798322f140b5203326a56a7 -/
import MCore.Core
import Mathlib

namespace MCore

/-- Problem-specific rescaling action. M-Core does not assume that unrelated
Millennium problems share the Navier–Stokes scaling map. -/
structure Scaling (U Λ : Type*) where
  act : Λ → U → U

/-- Scale criticality means invariance under the adapter's declared scaling. -/
def ScaleCritical {U Λ : Type*} (s : Scaling U Λ) (I : U → ℝ) : Prop :=
  ∀ λ u, I (s.act λ u) = I u

/-- Calibration constants are data, not theorems. -/
structure Calibration where
  phiObserved : ℝ := 0.6
  epsilonObserved : ℝ := 0.6
  samples : List ℝ := [0.309, 0.594, 0.609]

/-- A threshold is rigid only after a proof obligation certifies it. -/
structure CertifiedThreshold where
  value : ℝ
  positive : 0 < value
  belowOne : value < 1

end MCore


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/MCore/A2SelfRef.lean blob 6f6c6050664b759d30427ef696f13d42917723dc -/
import MCore.Core
import Mathlib

namespace MCore

inductive Node where
  | g1 | I | coeffA | targetY | g4
  deriving DecidableEq, Repr

abbrev Edge := Node × Node
abbrev Graph := List Edge

/-- A directed edge is explicitly present in the audit graph. -/
def HasEdge (G : Graph) (x y : Node) : Prop := (x, y) ∈ G

/-- The canonical forbidden self-reference pattern: I needs a, a needs Y,
and Y is established through I. -/
def HasCanonicalSelfRef (G : Graph) : Prop :=
  HasEdge G .I .coeffA ∧ HasEdge G .coeffA .targetY ∧ HasEdge G .targetY .I

/-- M-Core's DAG gate rejects the canonical cycle. -/
def PassesSelfRefGate (G : Graph) : Prop := ¬ HasCanonicalSelfRef G

example :
    ¬ PassesSelfRefGate [(.I, .coeffA), (.coeffA, .targetY), (.targetY, .I)] := by
  intro h
  apply h
  simp [HasCanonicalSelfRef, HasEdge]

end MCore


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/ATK/StructuralDefect.lean blob b2f8e24382fb4284e9a83116afb38926d7d8bafb -/
import Mathlib

namespace MCore.ATK.StructuralDefect

/-- The mathematical problems remain distinct. -/
inductive ProblemKind
  | riemann
  | pnp
  | yangMills
  | navierStokes
  | bsd
  | hodge
  | beal
deriving DecidableEq, Repr

/-- Closed taxonomy of structural gap shapes. -/
inductive GapShape
  | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8
deriving DecidableEq, Repr

/--
A problem-independent dynamical core.

The structural defect is deliberately discrete here.  This gives a
well-founded quantity: whenever the defect is non-zero, one structural
step must reduce it strictly.
-/
structure StructuralCore where
  State : Type
  step : State → State
  defect : State → Nat
  contract : ∀ x, 0 < defect x → defect (step x) < defect x

namespace StructuralCore

variable (C : StructuralCore)

/-- Terminality is intrinsic vanishing of the structural defect. -/
def Terminal (x : C.State) : Prop :=
  C.defect x = 0

/--
The contraction law cannot decrease forever: every state reaches
zero defect in finitely many structural steps.
-/
theorem zero_after_steps (x : C.State) :
    ∀ n : Nat, C.defect x ≤ n →
      ∃ k : Nat, k ≤ n ∧ C.defect ((C.step^[k]) x) = 0 := by
  intro n
  induction n generalizing x with
  | zero =>
      intro hx
      have hz : C.defect x = 0 := Nat.eq_zero_of_le_zero hx
      exact ⟨0, Nat.zero_le 0, by simpa using hz⟩
  | succ n ih =>
      intro hx
      by_cases hz : C.defect x = 0
      · exact ⟨0, Nat.zero_le (Nat.succ n), by simpa using hz⟩
      · have hpos : 0 < C.defect x := Nat.pos_of_ne_zero hz
        have hdec : C.defect (C.step x) < C.defect x :=
          C.contract x hpos
        have hnext : C.defect (C.step x) ≤ n := by
          omega
        obtain ⟨k, hk_le, hk_zero⟩ := ih (C.step x) hnext
        refine ⟨k + 1, ?_, ?_⟩
        · omega
        · simpa [Function.iterate_succ_apply] using hk_zero

/-- Canonical finite-time intrinsic closure theorem. -/
theorem intrinsic_vanishing (x : C.State) :
    ∃ k : Nat, k ≤ C.defect x ∧
      C.defect ((C.step^[k]) x) = 0 :=
  C.zero_after_steps x (C.defect x) (Nat.le_refl _)

end StructuralCore

/--
A manifestation does not identify the concrete mathematical object with
the structural core.  It only supplies an encoding and proves that
zero structural defect transports to that problem's terminal condition.
-/
structure Manifestation (P : ProblemKind) (C : StructuralCore) where
  ConcreteState : Type
  encode : ConcreteState → C.State
  terminal : ConcreteState → Prop
  decode : C.State → ConcreteState
  decode_encode : ∀ x, decode (encode x) = x
  terminal_of_zero :
    ∀ s : C.State, C.defect s = 0 → terminal (decode s)

/--
Universal structural transport.  This theorem is non-circular:
vanishing is obtained from strict descent of the intrinsic Nat-valued
defect, then transported through the problem-specific manifestation.
-/
theorem structural_number_closure
    {P : ProblemKind}
    (C : StructuralCore)
    (M : Manifestation P C)
    (x : M.ConcreteState) :
    ∃ k : Nat,
      k ≤ C.defect (M.encode x) ∧
      M.terminal (M.decode ((C.step^[k]) (M.encode x))) := by
  obtain ⟨k, hk, hz⟩ := C.intrinsic_vanishing (M.encode x)
  exact ⟨k, hk, M.terminal_of_zero _ hz⟩

/--
The shared object is the structural dynamics, not the concrete carrier.
Each problem may have a different concrete state type.
-/
theorem same_structure_not_same_object
    {P Q : ProblemKind}
    {C : StructuralCore}
    (MP : Manifestation P C)
    (MQ : Manifestation Q C) :
    Nonempty MP.ConcreteState → Nonempty MQ.ConcreteState →
      Nonempty MP.ConcreteState ∧ Nonempty MQ.ConcreteState := by
  intro hp hq
  exact ⟨hp, hq⟩

end MCore.ATK.StructuralDefect


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/MCore/Admissible.lean blob 42c138699f8bb10d047d6f9405e36ac6b9e8fbc5 -/
import MCore.A1Amplitude
import MCore.A2SelfRef
import MCore.A3Zero
import MCore.A4Scale

namespace MCore

/-- An adapter may enter S only by exposing all four audit obligations.
A1 is deliberately an obstruction flag rather than an assumption: degree-one
amplitude homogeneity plus a positive witness proves failure of a universal
fixed gap on an amplitude-unbounded class. -/
structure AuditRecord (U Λ : Type*) [AddCommGroup U] [Module ℝ U] where
  I : U → ℝ
  scaling : Scaling U Λ
  dependencyGraph : Graph
  amplitudeLaw : AmplitudeHomogeneous I
  selfRefGate : PassesSelfRefGate dependencyGraph
  zeroStatus : ZeroLocusStatus
  scaleLaw : ScaleCritical scaling I

/-- Membership is intentionally conservative: zero-locus totality is required.
Problem adapters can weaken/replace this only by proving a regularized total
extension and then constructing a new record for that extension. -/
def InS {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) : Prop :=
  R.zeroStatus = .total

end MCore


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/MCore/A1Amplitude.lean blob 261996779e5270ba15c8614b3f8e7de413de68ab -/
import MCore.Core
import Mathlib

namespace MCore

/-- Degree-one amplitude homogeneity on a real vector space. -/
def AmplitudeHomogeneous {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) : Prop :=
  ∀ (A : ℝ) (u : U), I (A • u) = A * I u

/-- A1: one positive witness rules out every universal fixed upper gap on an
amplitude-unbounded class. This is the precise theorem behind the heuristic
`sup_A I(Au)=∞`; no extended-real supremum machinery is needed. -/
theorem amplitude_unbounded
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) (hhom : AmplitudeHomogeneous I)
    {u : U} (hu : 0 < I u) :
    ∀ B : ℝ, ∃ A : ℝ, B < I (A • u) := by
  intro B
  let A : ℝ := (|B| + 1) / I u
  refine ⟨A, ?_⟩
  rw [hhom]
  dsimp [A]
  field_simp
  linarith [le_abs_self B]

/-- Corollary: no fixed `δ>0` can give `I ≤ 1-δ` for all amplitudes. -/
theorem no_fixed_delta_gap
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) (hhom : AmplitudeHomogeneous I)
    {u : U} (hu : 0 < I u) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, I (A • u) ≤ 1 - δ := by
  rintro ⟨δ, hδ, hgap⟩
  obtain ⟨A, hA⟩ := amplitude_unbounded I hhom hu (1 - δ)
  exact (not_lt_of_ge (hgap A)) hA

end MCore


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/Master.lean blob 42e8e6593133c9bd60df2394b63c4889816c2257 -/
import MCore.FinalFail.ExactGapLedger
import MCore.FinalFail.RecoveryFirewall
import MCore.FinalFail.DeltaIsolation
import MCore.FinalFail.ArtifactAttachment
import MCore.FinalFail.TriadicObstructionCalculus
import MCore.FinalFail.ClosedCenterHard
import MCore.FinalFail.FundamentalIndeterminacy
import MCore.FinalFail.RelationalHardAtom
import MCore.FinalFail.Attack.Beal
import MCore.FinalFail.Attack.NavierStokes

namespace MCore.FinalFail

def masterState : String :=
  "FINAL_FAIL: closed-center HARD + fundamental branching indeterminacy + relational brain kernel active; exact gaps pinned; no endpoint promoted"

def brainFoundationState : String :=
  "BRAIN_V1: START<->CENTER<->FINISH; branch-preserving relations; IFail is structural non-uniqueness, not numeric 0/0"

theorem master_open_count : openFinalProblems = 7 := openFinalProblems_eq_seven

end MCore.FinalFail


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalProofRegistry.lean blob da146e9aff03211b4a0eba3257bc8ca162773133 -/
import MCore.FinalFail.UniversalTerminalClosure
import MCore.FinalFail.RPAConfirmation
import MCore.FinalFail.RPALattice
import MCore.FinalFail.RPALatticeCube3

namespace MCore.FinalProof

inductive ProblemSlot where
  | riemann | beal | navierStokes | hodge | pVsNP | bsd | yangMills
  deriving DecidableEq, Repr

inductive SlotState where
  | linkedReuse
  | openMath
  | proved
  deriving DecidableEq, Repr

structure SlotRecord where
  slot : ProblemSlot
  sourceRepo : String
  sourceRef : String
  terminal : String
  state : SlotState
  deriving Repr

/-!
The registry records the current material terminal producer in each lane.
A GREEN/FROZEN reduction or transport certificate never changes a slot to
`proved`; only an inhabitant of the named terminal target may do that.
-/
def registry : List SlotRecord := [
  { slot := .riemann
    sourceRepo := "ShantiDraconis/m-core-riemann"
    sourceRef := "d6a291b4563f9021f74ab63cc983d44f079472da"
    terminal := "FiniteSpanApproximatesChi concreteGeneratorFamily"
    state := .openMath },
  { slot := .beal
    sourceRepo := "ShantiDraconis/m-core-beal"
    sourceRef := "d6fe130c44ef91e0f8ceb6b15a6548f186e381fd"
    terminal := "GCDLowerBoundProducer = ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)"
    state := .openMath },
  { slot := .navierStokes
    sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit"
    sourceRef := "df808543535d34d4e8c46096b3455d76b0151fa2"
    terminal := "ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    state := .openMath },
  { slot := .hodge
    sourceRepo := "ShantiDraconis/m-core-hodge"
    sourceRef := "42eaf7d4d639871f82eceb121ee525a6c4f30d84"
    terminal := "ConcreteAlgebraicityPayload"
    state := .openMath },
  { slot := .pVsNP
    sourceRepo := "ShantiDraconis/m-core-p-vs-np"
    sourceRef := "a3386d52951f2e886eca9359fc218cd18014e0f0"
    terminal := "Nonempty P01MachineConstruction ∧ G21Pointwise"
    state := .openMath },
  { slot := .bsd
    sourceRepo := "ShantiDraconis/m-core-bsd"
    sourceRef := "c1e7b245726c4c65f5f9f878acefb86460746f4a"
    terminal := "realizable elliptic-curve domain + universal rank equality + refined leading-coefficient identity"
    state := .openMath },
  { slot := .yangMills
    sourceRepo := "ShantiDraconis/m-core-yang-mills"
    sourceRef := "cd4bbfd348b607bd24ed0c6d605207b764286f58"
    terminal := "Nonempty (B60ConcretePhysicalAdapter C F D H G O)"
    state := .openMath }
]

def provedCount : Nat :=
  registry.foldl (fun n r => if r.state = .proved then n + 1 else n) 0

def openMathCount : Nat :=
  registry.foldl (fun n r => if r.state = .openMath then n + 1 else n) 0

theorem registry_length_eq_seven : registry.length = 7 := by
  decide

theorem provedCount_eq_zero : provedCount = 0 := by
  decide

theorem openMathCount_eq_seven : openMathCount = 7 := by
  decide

end MCore.FinalProof


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalProofFirewall.lean blob 98921e6eaaa33b1ecb8ac09a3ad50d3ac1ccd9ae -/
import MCore.FinalProofRegistry

namespace MCore.FinalProof

def FinalProofReady : Prop := provedCount = 7

theorem finalProof_not_ready : ¬ FinalProofReady := by
  simp [FinalProofReady, provedCount_eq_zero]

structure ExternalCertificateEligibility where
  allSevenProved : FinalProofReady

def FINAL_PROOF_DISPLAY : String := s!"{provedCount}/7"
def OPEN_MATH_DISPLAY : String := s!"{openMathCount}/7"

/-- Administrative consistency: all seven current slots are still material
OPEN_MATH, hence no final external certificate is eligible. -/
theorem final_registry_fail_closed :
    openMathCount = 7 ∧ provedCount = 0 := by
  exact ⟨openMathCount_eq_seven, provedCount_eq_zero⟩

#print axioms MCore.FinalProof.registry_length_eq_seven
#print axioms MCore.FinalProof.provedCount_eq_zero
#print axioms MCore.FinalProof.openMathCount_eq_seven
#print axioms MCore.FinalProof.finalProof_not_ready
#print axioms MCore.FinalProof.final_registry_fail_closed
#print axioms MCore.FinalFail.Universal.terminalInhabitants_iff_allSeven
#print axioms MCore.FinalFail.Universal.universal_aggregation_is_fail_closed

end MCore.FinalProof


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/RPALattice.lean blob 3f4d08972a7b8b1caf2780d97fdc2bae85551ab2 -/
import MCore.FinalFail.RPAConfirmation

namespace MCore.FinalFail.RPA

/-- Free multiplicity state before imposing idempotence. -/
structure EndpointMultiplicity where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def EndpointMultiplicity.add
    (a b : EndpointMultiplicity) : EndpointMultiplicity :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

instance : Add EndpointMultiplicity := ⟨EndpointMultiplicity.add⟩

def openAtom : EndpointMultiplicity := ⟨1, 0⟩
def closedAtom : EndpointMultiplicity := ⟨0, 1⟩

@[simp] theorem open_plus_open :
    openAtom + openAtom = ⟨2, 0⟩ := rfl

@[simp] theorem closed_plus_closed :
    closedAtom + closedAtom = ⟨0, 2⟩ := rfl

@[simp] theorem open_plus_closed :
    openAtom + closedAtom = ⟨1, 1⟩ := rfl

/-- Idempotent quotient: only presence/absence of each endpoint remains. -/
inductive CanonicalEndpointState
  | empty
  | open
  | closed
  | full
  deriving DecidableEq, Repr

def normalizeMultiplicity (s : EndpointMultiplicity) : CanonicalEndpointState :=
  match s.openCount = 0, s.closedCount = 0 with
  | true, true => .empty
  | false, true => .open
  | true, false => .closed
  | false, false => .full

@[simp] theorem normalize_open :
    normalizeMultiplicity openAtom = .open := by
  rfl

@[simp] theorem normalize_closed :
    normalizeMultiplicity closedAtom = .closed := by
  rfl

@[simp] theorem normalize_open_open :
    normalizeMultiplicity (openAtom + openAtom) = .open := by
  rfl

@[simp] theorem normalize_closed_closed :
    normalizeMultiplicity (closedAtom + closedAtom) = .closed := by
  rfl

@[simp] theorem normalize_open_closed :
    normalizeMultiplicity (openAtom + closedAtom) = .full := by
  rfl

def CanonicalSemantics
    (OpenMath ClosedMath : Prop) :
    CanonicalEndpointState → Prop
  | .empty => True
  | .open => OpenMath
  | .closed => ClosedMath
  | .full => DualEndpointState OpenMath ClosedMath

abbrev Full (OpenMath ClosedMath : Prop) : Prop :=
  CanonicalSemantics OpenMath ClosedMath .full

theorem full_iff_dual_endpoint_state
    (OpenMath ClosedMath : Prop) :
    Full OpenMath ClosedMath ↔
      DualEndpointState OpenMath ClosedMath :=
  Iff.rfl

theorem full_iff_global_external_certificate
    (OpenMath ClosedMath : Prop) :
    Full OpenMath ClosedMath ↔
      GlobalExternalCertificate OpenMath ClosedMath :=
  Iff.rfl

/-- Under idempotence, every positive OPEN multiplicity collapses to OPEN,
every positive CLOSED multiplicity collapses to CLOSED, and joint presence
collapses to FULL. -/
theorem normalize_positive_positive_full
    (n m : Nat)
    (hn : n ≠ 0)
    (hm : m ≠ 0) :
    normalizeMultiplicity ⟨n, m⟩ = .full := by
  simp [normalizeMultiplicity, hn, hm]

#print axioms MCore.FinalFail.RPA.normalize_positive_positive_full
#print axioms MCore.FinalFail.RPA.full_iff_dual_endpoint_state
#print axioms MCore.FinalFail.RPA.full_iff_global_external_certificate

end MCore.FinalFail.RPA


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/Attack/Beal.lean blob 4cffa2699e58327707686e969da9ab7822b5cc3a -/
import MCore.FinalFail.ArtifactAttachment

namespace MCore.FinalFail.Attack.Beal

structure PrimitiveReductionContract where
  statement : String
  sourceAnchor : String
  proved : Bool

structure ArithmeticProducerContract where
  statement : String
  required : List String
  forbidden : List String

def primitiveReduction : PrimitiveReductionContract := {
  statement := "reduce a hypothetical Beal counterexample to the exact primitive/common-divisor obstruction without changing the endpoint semantics"
  sourceAnchor := "m-core-beal BealSpecification + certified K9/K10 reductions"
  proved := false
}

def producer : ArithmeticProducerContract := {
  statement := "primitive BealData -> contradiction, hence nontrivial common divisor"
  required := ["exact primitive reduction", "valid theorem source for every imported arithmetic step", "endpoint CommonDivisor"]
  forbidden := ["assume CommonDivisor", "placeholder False", "unverified Frey/modularity/level-lowering route"]
}

def status : String :=
  "OPEN_MATH: no verified producer currently attached; Frey/modularity is a candidate route only, not an existing theorem chain"

end MCore.FinalFail.Attack.Beal


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/BoundaryAtoms.lean blob 53f0aadced7c97ee75d80dcb71ad96504de0e60a -/
import MCore.FinalFail.SevenLocalNuclei

namespace MCore.FinalFail

/-!
# Unconditional boundary atoms

Each active open problem receives a freely generated boundary atom.  These atoms
are unconditional formal objects of M-Core: they require no proof of the
corresponding external conjectural statement.

They are intentionally NOT identified definitionally with RH counterexamples,
Navier--Stokes stabilizers, Hodge cycles, SAT lower bounds, BSD identities,
Beal common-prime witnesses, or Yang--Mills realizations.  Such an
identification is a separate semantic interpretation and therefore cannot be
smuggled in by the datatype.
-/

/-- A freely generated formal inhabitant for each of the seven active boundary
slots.  This is the precise sense in which the boundary objects are now
unconditionally inhabited inside the formal hypothesis world. -/
inductive BoundaryAtom : ProblemId → Type
  | beal : BoundaryAtom .beal
  | navierStokes : BoundaryAtom .navierStokes
  | hodge : BoundaryAtom .hodge
  | pVsNP : BoundaryAtom .pVsNP
  | bsd : BoundaryAtom .bsd
  | riemann : BoundaryAtom .riemann
  | yangMills : BoundaryAtom .yangMills
  deriving Repr

/-- Every problem has a canonical boundary atom with no mathematical premise. -/
def boundaryAtom : (p : ProblemId) → BoundaryAtom p
  | .beal => .beal
  | .navierStokes => .navierStokes
  | .hodge => .hodge
  | .pVsNP => .pVsNP
  | .bsd => .bsd
  | .riemann => .riemann
  | .yangMills => .yangMills

theorem boundaryAtom_nonempty (p : ProblemId) :
    Nonempty (BoundaryAtom p) :=
  ⟨boundaryAtom p⟩

/-- Inventory of the seven unconditional formal inhabitants. -/
def unconditionalBoundaryInventory : List (Sigma BoundaryAtom) := [
  ⟨.riemann, .riemann⟩,
  ⟨.beal, .beal⟩,
  ⟨.navierStokes, .navierStokes⟩,
  ⟨.hodge, .hodge⟩,
  ⟨.pVsNP, .pVsNP⟩,
  ⟨.bsd, .bsd⟩,
  ⟨.yangMills, .yangMills⟩
]

def unconditionalFormalInhabitantCount : Nat :=
  unconditionalBoundaryInventory.length

theorem unconditionalFormalInhabitantCount_eq_seven :
    unconditionalFormalInhabitantCount = 7 := by
  decide

universe u

/-- Semantic interpretation is the explicit bridge from a free boundary atom to
a concrete target type.  Constructing this bridge is where the genuine
mathematical content must live. -/
structure BoundaryInterpretation
    (p : ProblemId) (Target : Sort u) where
  realize : BoundaryAtom p → Target

def realizeBoundary
    {p : ProblemId} {Target : Sort u}
    (I : BoundaryInterpretation p Target) : Target :=
  I.realize (boundaryAtom p)

theorem interpretedBoundary_nonempty
    {p : ProblemId} {Target : Sort u}
    (I : BoundaryInterpretation p Target) :
    Nonempty Target :=
  ⟨realizeBoundary I⟩


/-- Semantic firewall: because every BoundaryAtom is already inhabited, producing
an interpretation is exactly as strong (at the level of inhabitance) as
producing the classical target itself.  The formal atom therefore cannot make
the external mathematics easier by itself. -/
theorem nonempty_boundaryInterpretation_iff_nonempty_target
    {p : ProblemId} {Target : Sort u} :
    Nonempty (BoundaryInterpretation p Target) ↔ Nonempty Target := by
  constructor
  · rintro ⟨I⟩
    exact ⟨I.realize (boundaryAtom p)⟩
  · rintro ⟨t⟩
    exact ⟨{ realize := fun _ => t }⟩

end MCore.FinalFail


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/DeltaIsolation.lean blob 8dab4ed10a59305ffc76aa8e249ebcc66d0c41be -/
import MCore.FinalFail.ExactGapLedger

namespace MCore.FinalFail

structure IsolatedDelta where
  problem : String
  deltaStatement : String
  requiredMachinery : List String
  forbiddenShortcut : List String
  sourceAnchor : String
  deriving Repr

def isolatedDeltas : List IsolatedDelta := [
  { problem := "BEAL", deltaStatement := "primitive Beal solution -> contradiction/common divisor", requiredMachinery := ["primitive reduction", "genuine arithmetic producer"], forbiddenShortcut := ["assume CommonDivisor", "invent Frey/modularity bridge without theorem source"], sourceAnchor := "BealSpecification + K9/K10" },
  { problem := "POINCARE", deltaStatement := "faithful formal import of the historically closed chain to S3", requiredMachinery := ["formal 3-manifold endpoint", "verified known-proof dependencies"], forbiddenShortcut := ["PoincareResolved -> PoincareResolved", "True endpoint"], sourceAnchor := "positive-control source still to pin at theorem level" },
  { problem := "NAVIER_STOKES", deltaStatement := "independent compensator budget + quantitative signed cancellation + OPEN_CZ positive scale gain", requiredMachinery := ["T_cross tensor", "independent compensator", "signed CZ estimate"], forbiddenShortcut := ["C_N := -T_N", "absolute bound substituted for signed gain"], sourceAnchor := "audit/09_required_cancellations.md; audit/76_stretchFar_signed_blocking.md" },
  { problem := "HODGE", deltaStatement := "rational Hodge class -> rational span of algebraic cycle classes", requiredMachinery := ["general algebraicity/surjectivity"], forbiddenShortcut := ["store algebraic cycle inside input class"], sourceAnchor := "Hodge.lean; R3a frozen provenance" },
  { problem := "P_VS_NP", deltaStatement := "construct official-model language with genuine asymptotic not_in_p proof", requiredMachinery := ["official model match", "universal asymptotic lower bound"], forbiddenShortcut := ["finite C12 evidence -> universal lower bound", "witness supplied as hypothesis"], sourceAnchor := "EndpointCompression; ThreeTracks; K10" },
  { problem := "BSD", deltaStatement := "for every arithmetic-analytic datum, analyticOrderAtOne = mordellWeilRank", requiredMachinery := ["universal rank/order theorem"], forbiddenShortcut := ["particular curves -> all curves", "numerical approximation -> exact equality"], sourceAnchor := "K12; ThreeWorldClosure recovery" },
  { problem := "RIEMANN", deltaStatement := "concrete DNLimit=0 plus independently verified DNLimit=0 iff RH", requiredMachinery := ["exact vanishing estimate", "unconditional endpoint equivalence"], forbiddenShortcut := ["DNLimit approximately zero -> zero", "conditional bridge -> unconditional bridge"], sourceAnchor := "BackwardDenseEndpoint.lean; K8 ad3011f1..." },
  { problem := "YANG_MILLS", deltaStatement := "genuine 4D construction/OS reconstruction plus positive physical spectral gap", requiredMachinery := ["4D continuum construction", "OS/Hamiltonian identification", "spectral positivity"], forbiddenShortcut := ["inhabited abstract structure", "correlation decay alone -> physical mass gap"], sourceAnchor := "K21 0352c6af...; hardened physical interfaces" }
]

def deltaFor? (problem : String) : Option IsolatedDelta :=
  isolatedDeltas.find? (fun d => d.problem == problem)

end MCore.FinalFail


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/ExactGapLedger.lean blob b1e8bf78f8c38cb682fff19d092bcdc6b908c802 -/
import MCore.FinalFail.SevenLocalNuclei

namespace MCore.FinalFail

inductive GapState where
  | proved | historicallySolvedToAudit | openMath | externalBridge
  deriving DecidableEq, Repr

inductive ResolutionShape where
  | nonexistence | elimination | vanishing | quotientZero
  | separation | equality | bridgeAndVanishing | positivity
  deriving DecidableEq, Repr

structure ExactGap where
  problem : String
  statement : String
  resolution : ResolutionShape
  state : GapState
  source : String
  provenance : String
  deriving Repr

def exactGaps : List ExactGap := [
  { problem := "BEAL", statement := "primitive/common-gcd=1 Beal equation -> contradiction; equivalently every BealData has a nontrivial common divisor", resolution := .nonexistence, state := .openMath, source := "m-core-beal/lean/MCore/BealSpecification.lean + K9/K10", provenance := "K6 frozen 434d6b7b...; K9 frozen e3b8598a..." },
  { problem := "POINCARE", statement := "faithfully import the known geometrization/Ricci-flow-with-surgery chain through recognition M ~= S3", resolution := .elimination, state := .historicallySolvedToAudit, source := "positive-control import pending exact theorem-level formal source", provenance := "historically solved; not counted as a new FINAL_PROOF result" },
  { problem := "NAVIER_STOKES", statement := "construct a legitimate compensator with independent quantitative budget and prove signed far-field direction-field cancellation with positive scale gain", resolution := .vanishing, state := .openMath, source := "navier-stokes-critical-barrier-audit/audit/76_stretchFar_signed_blocking.md + audit/09_required_cancellations.md", provenance := "fail-proof run 35565581964 GREEN; no endpoint promotion" },
  { problem := "HODGE", statement := "for every smooth projective X and rational Hodge class alpha, produce rational span of algebraic cycle classes", resolution := .quotientZero, state := .openMath, source := "m-core-hodge Hodge.lean + R3a provenance", provenance := "R3a frozen/audited reduction; general algebraicity remains open" },
  { problem := "P_VS_NP", statement := "produce a genuine asymptotic SAT lower bound in the fixed official model yielding not_in_p", resolution := .separation, state := .openMath, source := "m-core-p-vs-np EndpointCompression/ThreeTracks/K10", provenance := "historical triadic source recovered and hash-pinned; ApproximationBridge remains open" },
  { problem := "BSD", statement := "prove universally analyticOrderAtOne = mordellWeilRank; full BSD additionally needs the leading-coefficient arithmetic identity", resolution := .equality, state := .openMath, source := "m-core-bsd K12 + ThreeWorldClosure/NumericClasses recovery", provenance := "certified architecture preserves substantive rank equality as open" },
  { problem := "RIEMANN", statement := "prove concrete DNLimit=0 and independently prove/audit DNLimit=0 iff RiemannHypothesis", resolution := .bridgeAndVanishing, state := .openMath, source := "m-core-riemann/BackwardDenseEndpoint.lean", provenance := "K8 GREEN run 35565114760 SHA ad3011f1...; K8 not to be redone" },
  { problem := "YANG_MILLS", statement := "construct genuine 4D continuum theory with OS reconstruction/Hamiltonian identification and prove a positive spectral mass gap", resolution := .positivity, state := .openMath, source := "m-core-yang-mills hardened physical interfaces + K21/K14", provenance := "K21 GREEN 0352c6af...; fail-proof 35518892629 forbids trivial physical interfaces" }
]

def openFinalProblems : Nat :=
  exactGaps.foldl (fun n g => if g.state = .openMath then n + 1 else n) 0

theorem openFinalProblems_eq_seven : openFinalProblems = 7 := by decide

end MCore.FinalFail


/- https://github.com/ShantiDraconis/M-Core/blob/01d8d7660ccfea0285628bd7c5de33a661c4b77c/lean/MCore/FinalFail/RPALatticeCube3.lean blob 6ca8f3c1eeb556611224c8e3d3ab4472e24bbef5 -/
import MCore.FinalFail.RPALattice

namespace MCore.FinalFail.RPA

inductive EndpointAtom
  | open
  | closed
  deriving DecidableEq, Repr

abbrev EndpointWord := List EndpointAtom

def W_OPEN : EndpointWord := [.open]
def W_CLOSED : EndpointWord := [.closed]

def W_OPEN_CLOSED : EndpointWord := [.open, .closed]
def W_CLOSED_OPEN : EndpointWord := [.closed, .open]
def W_OPEN_OPEN : EndpointWord := [.open, .open]
def W_CLOSED_CLOSED : EndpointWord := [.closed, .closed]

def W_OPEN_OPEN_OPEN : EndpointWord := [.open, .open, .open]
def W_CLOSED_CLOSED_CLOSED : EndpointWord := [.closed, .closed, .closed]
def W_OPEN_OPEN_CLOSED : EndpointWord := [.open, .open, .closed]
def W_OPEN_CLOSED_OPEN : EndpointWord := [.open, .closed, .open]
def W_CLOSED_OPEN_OPEN : EndpointWord := [.closed, .open, .open]
def W_OPEN_CLOSED_CLOSED : EndpointWord := [.open, .closed, .closed]
def W_CLOSED_OPEN_CLOSED : EndpointWord := [.closed, .open, .closed]
def W_CLOSED_CLOSED_OPEN : EndpointWord := [.closed, .closed, .open]

def W_FULL : EndpointWord := [.open, .open, .closed, .closed]

def wordMultiplicity (w : EndpointWord) : EndpointMultiplicity :=
  w.foldl
    (fun s a =>
      match a with
      | .open => s + openAtom
      | .closed => s + closedAtom)
    ⟨0, 0⟩

def normalizeWord (w : EndpointWord) : CanonicalEndpointState :=
  normalizeMultiplicity (wordMultiplicity w)

@[simp] theorem norm_OPEN :
    normalizeWord W_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED :
    normalizeWord W_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_CLOSED :
    normalizeWord W_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN :
    normalizeWord W_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_OPEN_OPEN :
    normalizeWord W_OPEN_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED_CLOSED :
    normalizeWord W_CLOSED_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_OPEN_OPEN :
    normalizeWord W_OPEN_OPEN_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED_CLOSED_CLOSED :
    normalizeWord W_CLOSED_CLOSED_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_OPEN_CLOSED :
    normalizeWord W_OPEN_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_OPEN_CLOSED_OPEN :
    normalizeWord W_OPEN_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN_OPEN :
    normalizeWord W_CLOSED_OPEN_OPEN = .full := by rfl

@[simp] theorem norm_OPEN_CLOSED_CLOSED :
    normalizeWord W_OPEN_CLOSED_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN_CLOSED :
    normalizeWord W_CLOSED_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_CLOSED_OPEN :
    normalizeWord W_CLOSED_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_FULL :
    normalizeWord W_FULL = .full := by rfl

def WordSemantics
    (OpenMath ClosedMath : Prop)
    (w : EndpointWord) : Prop :=
  CanonicalSemantics OpenMath ClosedMath (normalizeWord w)

theorem full_word_iff_global_external_certificate
    (OpenMath ClosedMath : Prop) :
    WordSemantics OpenMath ClosedMath W_FULL ↔
      GlobalExternalCertificate OpenMath ClosedMath := by
  rfl

theorem all_length3_mixed_words_are_full
    (OpenMath ClosedMath : Prop) :
    (WordSemantics OpenMath ClosedMath W_OPEN_OPEN_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_OPEN_CLOSED_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_OPEN_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_OPEN_CLOSED_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_OPEN_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_CLOSED_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

#print axioms MCore.FinalFail.RPA.norm_OPEN_OPEN
#print axioms MCore.FinalFail.RPA.norm_CLOSED_CLOSED
#print axioms MCore.FinalFail.RPA.norm_OPEN_OPEN_OPEN
#print axioms MCore.FinalFail.RPA.norm_CLOSED_CLOSED_CLOSED
#print axioms MCore.FinalFail.RPA.all_length3_mixed_words_are_full
#print axioms MCore.FinalFail.RPA.full_word_iff_global_external_certificate

end MCore.FinalFail.RPA

