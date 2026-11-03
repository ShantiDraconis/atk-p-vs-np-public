import MCore.C11.BranchingCost
import MCore.Real.P02BoundedComputationEncoding
import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02RestrictionLowerBoundPattern

open C9 C10 C11 CircuitK1 CircuitC2
open P02BoundedComputationEncoding

/-- Idempotence of the repository simplifier. -/
theorem simplify_idempotent (t : Circuit) :
    CircuitC2.simplify (CircuitC2.simplify t) = CircuitC2.simplify t := by
  induction t with
  | input i => rfl
  | const b => rfl
  | not t ih =>
      simp only [CircuitC2.simplify]
      cases h : CircuitC2.simplify t with
      | input i => simp_all [CircuitC2.simplify]
      | const b => cases b <;> simp_all [CircuitC2.simplify]
      | not d => simp_all [CircuitC2.simplify]
      | and a b => simp_all [CircuitC2.simplify]
      | or a b => simp_all [CircuitC2.simplify]
  | and a b iha ihb =>
      simp only [CircuitC2.simplify]
      cases ha : CircuitC2.simplify a <;>
      cases hb : CircuitC2.simplify b <;>
        simp_all [CircuitC2.simplify] <;>
        split <;> simp_all [CircuitC2.simplify]
  | or a b iha ihb =>
      simp only [CircuitC2.simplify]
      cases ha : CircuitC2.simplify a <;>
      cases hb : CircuitC2.simplify b <;>
        simp_all [CircuitC2.simplify] <;>
        split <;> simp_all [CircuitC2.simplify]

/-- Restricting by the everywhere-free restriction is syntactic identity. -/
theorem restrict_leavesZeroFree (t : Circuit) :
    restrict leavesZeroFree t = t := by
  induction t with
  | input i => simp [restrict, leavesZeroFree]
  | const b => rfl
  | not t ih => simp [restrict, ih]
  | and a b iha ihb => simp [restrict, iha, ihb]
  | or a b iha ihb => simp [restrict, iha, ihb]

/-- Canonical normalized CNF bridge: normalize exactly once at the boundary. -/
def cnfCircuitNorm (f : CNF) : Circuit :=
  CircuitC2.simplify (cnfCircuit f)

/-- Local Lane-4 normalized dynamics: the initial formula is simplified before
the restriction is applied, so representation-only simplification cannot count
as progress. -/
def DNorm (ρ : Restriction) (t : FormulaTree) : FormulaTree :=
  CircuitC2.simplify (restrict ρ (CircuitC2.simplify t))

def RestrictionProgressNorm (ρ : Restriction) (t : FormulaTree) : Prop :=
  DNorm ρ t ≠ CircuitC2.simplify t

def amortizedDropNorm (ρ : Restriction) (t : FormulaTree) : Nat :=
  CircuitK1.size (CircuitC2.simplify t) - CircuitK1.size (DNorm ρ t)

/-- Exact amortized structural drop used by C11, evaluated on the canonical
Circuit view of a CNF. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

def PersistentBranchingDeficit
    (α β : Nat) (t : FormulaTree) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ t →
      amortizedDrop α β ρ t ≤ costBits ρ t

theorem persistentBranchingDeficit_excludes_payoff
    (α β : Nat) (t : FormulaTree)
    (h : PersistentBranchingDeficit α β t) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ t →
        ¬ PaysOff α β ρ t := by
  intro ρ hprog hpay
  have hlt := paysOff_implies_costBits_lt_amortizedDrop α β ρ t hpay
  have hle := h ρ hprog
  omega

/-- Canonical CNF variable bound: one plus the largest variable identifier. -/
def clauseVarBound (c : Clause) : Nat :=
  c.foldl (fun acc l => max acc (l.var + 1)) 0

def cnfVarBound (f : CNF) : Nat :=
  f.foldl (fun acc c => max acc (clauseVarBound c)) 0

/-- General bounded CNF family over the repository's canonical CNF type.
This is useful as an ambient family, but is not claimed to satisfy a persistent
deficit universally. -/
def GeneralCNFFamily
    (clauseBound : Nat → Nat) (n : Nat) (f : CNF) : Prop :=
  cnfVarBound f ≤ n ∧ f.length ≤ clauseBound n

/-- A hard subfamily is a predicate on the canonical CNF type, refined by the
same explicit size envelope used by the reduction. -/
def HardCNFSubfamily
    (IsHardCNF : CNF → Prop)
    (clauseBound : Nat → Nat)
    (n : Nat) (f : CNF) : Prop :=
  IsHardCNF f ∧ GeneralCNFFamily clauseBound n f

/-- A single canonical CNF has a uniform local branching deficit of at least c. -/
def DeficitAtLeast (c : Nat) (f : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit f) →
      amortizedDrop 1 1 ρ (cnfCircuit f) ≤
        costBits ρ (cnfCircuit f) ∧
      c ≤ costBits ρ (cnfCircuit f) -
        amortizedDrop 1 1 ρ (cnfCircuit f)

/-- Representation-invariant Lane-4 deficit: only restriction-induced
progress after normalization is counted. -/
def DeficitAtLeastNorm (c : Nat) (f : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgressNorm ρ (cnfCircuitNorm f) →
      amortizedDropNorm ρ (cnfCircuitNorm f) ≤
        costBits ρ (cnfCircuitNorm f) ∧
      c ≤ costBits ρ (cnfCircuitNorm f) -
        amortizedDropNorm ρ (cnfCircuitNorm f)

theorem simplify_cnfCircuitNorm_idem (f : CNF) :
    CircuitC2.simplify (cnfCircuitNorm f) = cnfCircuitNorm f := by
  unfold cnfCircuitNorm
  exact simplify_idempotent _

theorem leavesZeroFree_no_progress_norm (f : CNF) :
    ¬ RestrictionProgressNorm leavesZeroFree (cnfCircuitNorm f) := by
  unfold RestrictionProgressNorm DNorm cnfCircuitNorm
  rw [simplify_idempotent]
  rw [restrict_leavesZeroFree]
  exact fun h => h (simplify_idempotent _)

/-- Hard canonical-CNF subfamily.  The hardness predicate is not a new syntax:
it is a semantic/quantitative filter on the repository's existing CNF type. -/
def HardCNFSubfamilyWithMargin
    (c : Nat)
    (clauseBound : Nat → Nat)
    (n : Nat) (f : CNF) : Prop :=
  GeneralCNFFamily clauseBound n f ∧ DeficitAtLeast c f

theorem hardCNF_excludes_payoff
    {c : Nat} {f : CNF}
    (hc : 0 < c)
    (h : DeficitAtLeast c f) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ (cnfCircuit f) →
        ¬ PaysOff 1 1 ρ (cnfCircuit f) := by
  intro ρ hprog hpay
  have hdef := (h ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop
      1 1 ρ (cnfCircuit f) hpay
  omega

/-- Uniform positive deficit on every progressing restriction of every member
of a parametrized canonical-CNF family. -/
def UniformPersistentDeficit
    (Family : Nat → CNF → Prop) : Prop :=
  ∃ (c n0 : Nat), 0 < c ∧
    ∀ n : Nat, n0 ≤ n →
      ∀ f : CNF, Family n f →
        ∀ ρ : Restriction,
          RestrictionProgress ρ (cnfCircuit f) →
            amortizedDrop 1 1 ρ (cnfCircuit f) ≤
              costBits ρ (cnfCircuit f) ∧
            c ≤ costBits ρ (cnfCircuit f) -
              amortizedDrop 1 1 ρ (cnfCircuit f)

abbrev PersistentBranchingDeficitFamily :=
  UniformPersistentDeficit

theorem hardSubfamily_has_uniform_deficit
    {c : Nat} (hc : 0 < c)
    (clauseBound : Nat → Nat) :
    UniformPersistentDeficit
      (HardCNFSubfamilyWithMargin c clauseBound) := by
  refine ⟨c, 0, hc, ?_⟩
  intro n hn f hf ρ hprog
  exact hf.2 ρ hprog

theorem uniformPersistentDeficit_excludes_eventual_payoff
    {Family : Nat → CNF → Prop}
    (h : UniformPersistentDeficit Family) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ f : CNF, Family n f →
        ∀ ρ : Restriction,
          RestrictionProgress ρ (cnfCircuit f) →
            ¬ PaysOff 1 1 ρ (cnfCircuit f) := by
  rcases h with ⟨c, n0, hc, h⟩
  refine ⟨n0, ?_⟩
  intro n hn f hf ρ hprog hpay
  have hdef := (h n hn f hf ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop
      1 1 ρ (cnfCircuit f) hpay
  omega

/-- A restriction is core-dominated when it gives progress on the padded
formula and independently gives progress on the hard core.  This excludes the
vacuous empty-core counterexample and records the exact guard needed by the
inheritance theorem. -/
def CoreDominatedProgress
    (ρ : Restriction)
    (f core : CNF) : Prop :=
  RestrictionProgress ρ (cnfCircuit (f ++ core)) ∧
  RestrictionProgress ρ (cnfCircuit core)

/-- Guarded deficit inheritance.  Unlike raw append inheritance, this only
claims inheritance for restrictions whose progress is witnessed on the core. -/
def CoreDominatedDeficitInheritance
    (core : Nat → CNF)
    (c : Nat) : Prop :=
  ∀ (n : Nat) (f : CNF) (ρ : Restriction),
    DeficitAtLeast c (core n) →
    CoreDominatedProgress ρ f (core n) →
      amortizedDrop 1 1 ρ (cnfCircuit (f ++ core n)) ≤
        costBits ρ (cnfCircuit (f ++ core n)) ∧
      c ≤ costBits ρ (cnfCircuit (f ++ core n)) -
        amortizedDrop 1 1 ρ (cnfCircuit (f ++ core n))

/-- A usable hard-core family for the guarded padding route. -/
structure HardCoreFamily where
  core : Nat → CNF
  margin : Nat
  margin_pos : 0 < margin
  satisfiable :
    ∀ n, SATLanguage (cnfCircuit (core n))
  deficit :
    ∀ n, DeficitAtLeast margin (core n)
  dominated_inherits :
    CoreDominatedDeficitInheritance core margin

/-- Polynomial SAT reduction into a parametrized family of canonical CNFs. -/
structure SATReductionIntoFamily
    (Family : Nat → CNF → Prop) where
  reduce : CanonicalFinalProof.BitString → CNF
  parameter : CanonicalFinalProof.BitString → Nat
  parameterBound : Nat → Nat
  parameter_poly : CanonicalFinalProof.PolynomialTimeBound parameterBound
  parameter_le : ∀ x : CanonicalFinalProof.BitString, parameter x ≤ parameterBound (List.length x)
  lands : ∀ x : CanonicalFinalProof.BitString, Family (parameter x) (reduce x)
  correct :
    ∀ x : CanonicalFinalProof.BitString,
      CanonicalSATBoundary.SATBits
          CanonicalCircuitBits.circuitBitEncoding x ↔
        SATLanguage (cnfCircuit (reduce x))

/-- Exact dominance obligation needed by the guarded route: every restriction
that makes progress on the padded output must also make progress on the core. -/
def CoreProgressDominates
    (payload core : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit (payload ++ core)) →
      RestrictionProgress ρ (cnfCircuit core)

/-- Core-aware progress is intentionally separate from C10.RestrictionProgress.
It cannot replace the original notion globally. -/
def CoreAwareProgress
    (ρ : Restriction)
    (payload core : CNF) : Prop :=
  RestrictionProgress ρ (cnfCircuit (payload ++ core)) ∧
  RestrictionProgress ρ (cnfCircuit core)

def CoreAwareProgressCoverage
    (payload core : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit (payload ++ core)) →
      CoreAwareProgress ρ payload core

theorem coreAwareCoverage_implies_coreProgressDominates
    {payload core : CNF}
    (h : CoreAwareProgressCoverage payload core) :
    CoreProgressDominates payload core := by
  intro ρ hprog
  exact (h ρ hprog).2

theorem coreProgressDominates_to_coreDominated
    {payload core : CNF}
    (h : CoreProgressDominates payload core) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ (cnfCircuit (payload ++ core)) →
        CoreDominatedProgress ρ payload core := by
  intro ρ hprog
  exact ⟨hprog, h ρ hprog⟩

/-- Variables occurring in the canonical CNF payload. -/
def cnfVarList (f : CNF) : List Nat :=
  (f.flatMap fun clause => clause.map Literal.var).eraseDups

/-- Symmetric coupling gadget for a payload variable v.  Two fresh auxiliaries
ensure that either Boolean value of v extends to a satisfying assignment:
(v ∨ a_v) ∧ (¬v ∨ b_v). -/
def coverageClauses (base i v : Nat) : CNF :=
  [ [pos v, pos (base + 2 * i)]
  , [neg v, pos (base + 2 * i + 1)] ]

/-- Total-variable coverage core: every payload variable occurs in both
polarities, coupled to fresh auxiliaries.  This layer is semantic/coverage
infrastructure only; no deficit claim is attached here. -/
def coverageCore (payload : CNF) : CNF :=
  let base := cnfVarBound payload
  ((cnfVarList payload).enum.flatMap
    (fun vi => coverageClauses base vi.1 vi.2))

theorem evalCNF_append
    (σ : Assignment) (a b : CNF) :
    evalCNF σ (a ++ b) = (evalCNF σ a && evalCNF σ b) := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
      simp [evalCNF, ih, Bool.and_assoc]

theorem coverageClauses_allTrue
    (base i v : Nat) :
    evalCNF (fun _ => true) (coverageClauses base i v) = true := by
  simp [coverageClauses, evalCNF, evalClause, evalLiteral, pos, neg]

theorem coverageList_allTrue
    (base : Nat) (xs : List (Nat × Nat)) :
    evalCNF (fun _ => true)
      (xs.flatMap (fun vi => coverageClauses base vi.1 vi.2)) = true := by
  induction xs with
  | nil => rfl
  | cons vi xs ih =>
      simp only [List.flatMap_cons]
      rw [evalCNF_append]
      simp [coverageClauses_allTrue, ih]

/-- The coverage core is satisfiable by the all-true assignment. -/
theorem coverageCore_sat (payload : CNF) :
    SATLanguage (cnfCircuit (coverageCore payload)) := by
  rw [satLanguage_cnfCircuit_iff]
  refine ⟨fun _ => true, ?_⟩
  unfold coverageCore
  exact coverageList_allTrue (cnfVarBound payload) (cnfVarList payload).enum

/-- Nonempty whenever the payload has at least one syntactic CNF variable. -/
theorem coverageCore_nonempty
    (payload : CNF)
    (h : cnfVarList payload ≠ []) :
    coverageCore payload ≠ [] := by
  unfold coverageCore
  cases hv : (cnfVarList payload).enum with
  | nil =>
      have : cnfVarList payload = [] := by
        simpa using hv
      exact (h this).elim
  | cons x xs =>
      simp [coverageClauses]

/-- Exact remaining coverage obligation for the total-variable gadget.
Because C10 progress also observes simplification, membership of every payload
variable in the core is necessary but not by itself used as a proof here. -/
def TotalVariableCoverageObligation (payload : CNF) : Prop :=
  CoreAwareProgressCoverage payload (coverageCore payload)


/-- Reduction specialized to the hard-core construction.  Besides semantic
correctness, it must expose that every progressing restriction relevant to the
lower-bound argument is core-dominated. -/
structure SATReductionIntoCoreDominatedFamily
    (H : HardCoreFamily)
    (Family : Nat → CNF → Prop) extends SATReductionIntoFamily Family where
  payload : CanonicalFinalProof.BitString → CNF
  reduce_eq :
    ∀ x : CanonicalFinalProof.BitString, reduce x = payload x ++ H.core (parameter x)
  progress_coverage :
    ∀ x : CanonicalFinalProof.BitString,
      CoreAwareProgressCoverage (payload x) (H.core (parameter x))
  progress_dominance :
    ∀ x : CanonicalFinalProof.BitString,
      CoreProgressDominates (payload x) (H.core (parameter x)) := by
    intro x
    exact coreAwareCoverage_implies_coreProgressDominates
      (progress_coverage x)
  every_progress_core_dominated :
    ∀ (x : CanonicalFinalProof.BitString) (ρ : Restriction),
      RestrictionProgress ρ (cnfCircuit (reduce x)) →
      CoreDominatedProgress ρ (payload x) (H.core (parameter x)) := by
    intro x ρ hprog
    rw [reduce_eq x] at hprog
    exact coreProgressDominates_to_coreDominated
      (progress_dominance x) ρ hprog

/-- Explicit simulation obligation: a polynomial DTM for canonical SAT must
induce a restriction-tree procedure on the hard family. The theorem carrying
the exponential lower bound belongs here; it is not inferred from C11 alone. -/
structure DTMToRestrictionTreeAdapter
    (Family : Nat → CNF → Prop) where
  deficit_excludes_poly_sat :
    Nonempty (SATReductionIntoFamily Family) →
    UniformPersistentDeficit Family →
    ¬ CanonicalFinalProof.InP
      (CanonicalSATBoundary.SATBits
        CanonicalCircuitBits.circuitBitEncoding)

def RestrictionLowerBoundTransfer
    (Family : Nat → CNF → Prop) : Prop :=
  Nonempty (SATReductionIntoFamily Family) ∧
  Nonempty (DTMToRestrictionTreeAdapter Family) ∧
  UniformPersistentDeficit Family

theorem transfer_closes_p02
    {Family : Nat → CNF → Prop}
    (h : RestrictionLowerBoundTransfer Family) :
    P02TerminalFrontier.P02Target := by
  rcases h with ⟨hRed, hAdapter, hDeficit⟩
  rcases hAdapter with ⟨A⟩
  exact P02TerminalFrontier.p02_target_iff_sat_not_in_p.mpr
    (A.deficit_excludes_poly_sat hRed hDeficit)

#print axioms MCore.Real.P02RestrictionLowerBoundPattern.paysOff_implies_costBits_lt_amortizedDrop
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentBranchingDeficit_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.hardCNF_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.hardSubfamily_has_uniform_deficit
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.uniformPersistentDeficit_excludes_eventual_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.coreAwareCoverage_implies_coreProgressDominates
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.coreProgressDominates_to_coreDominated
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.transfer_closes_p02

end P02RestrictionLowerBoundPattern
end Real
end MCore
