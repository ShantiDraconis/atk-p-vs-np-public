import MCore.Real.P02AntiModels
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace P03MaterialLaw

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P02ComplementRunRealization
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P02OddSemanticRecurrence

/--
The three concrete clause regions of the bounded Cook--Levin tableau.
This classification is syntactic and contains no semantic endpoint.
-/
inductive ClausePhase where
  | init
  | transit
  | terminal
  deriving DecidableEq, Repr

/-- A CNF is unsatisfiable when no Boolean assignment satisfies it. -/
def CNFUnsat (F : NTMCNF) : Prop :=
  ∀ sigma : Assignment, evalNTMCNF sigma F = false

/-- A CNF is satisfiable when some Boolean assignment satisfies it. -/
def CNFSat (F : NTMCNF) : Prop :=
  ∃ sigma : Assignment, evalNTMCNF sigma F = true

/-- Concrete clause block selected by a phase. -/
def phaseCNF
    (phase : ClausePhase)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  match phase with
  | .init => ntmInitialCNF M x t
  | .transit => ntmTransitionsCNF M x t
  | .terminal => ntmFinalAcceptanceCNF M t

/--
A support mask for a clause-level conflict.  Unlike the discarded single-phase
extractor, this allows UNSAT to be caused by compatibility constraints spanning
multiple tableau regions.
-/
structure ClauseConflictSupport where
  init : Bool
  transit : Bool
  terminal : Bool
  nonempty : init = true ∨ transit = true ∨ terminal = true
  deriving Repr

/-- CNF selected by a conflict-support mask. -/
def supportedCNF
    (S : ClauseConflictSupport)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  (if S.init then ntmInitialCNF M x t else []) ++
  (if S.transit then ntmTransitionsCNF M x t else []) ++
  (if S.terminal then ntmFinalAcceptanceCNF M t else [])

/--
A genuine clause-conflict witness.  It records only which concrete blocks are
needed for an unsatisfiable conjunction; no acceptance predicate is stored.
-/
structure ClauseConflictWitness
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  support : ClauseConflictSupport
  unsat : CNFUnsat (supportedCNF support M x t)

/--
Fail-closed extractor target.  Whole-tableau UNSAT always has a legal support
candidate (all three blocks), while later mathematics may prove a smaller or
structured support.  This avoids the false implication
  UNSAT (A ∧ B ∧ C) -> UNSAT A ∨ UNSAT B ∨ UNSAT C.
-/
structure ClauseConflictExtractor
    (M : PolyNTMCandidate) where
  locate :
    ∀ (x : BitString) (t : Nat),
      CNFUnsat (boundedExecTableauCNF_NTM M x t) →
      ClauseConflictWitness M x t

/-- The full three-block support. -/
def fullSupport : ClauseConflictSupport where
  init := true
  transit := true
  terminal := true
  nonempty := Or.inl rfl

@[simp] theorem supportedCNF_fullSupport
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    supportedCNF fullSupport M x t =
      boundedExecTableauCNF_NTM M x t := by
  rfl

/--
The conflict extractor itself is structural, not OPEN_MATH: on an UNSAT full
tableau, selecting all three actual blocks is a valid clause-level witness.
The hard mathematics is to refine this support into parity mixing.
-/
def fullConflictExtractor
    (M : PolyNTMCandidate) :
    ClauseConflictExtractor M where
  locate := by
    intro x t hUnsat
    exact
      { support := fullSupport
        unsat := by
          simpa using hUnsat }

/--
A phase observation is now tied to an actual clause-conflict witness.
The phase label is not allowed to float independently of the CNF evidence.
-/
structure ClausePhaseObservation
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  conflict : ClauseConflictWitness M x t
  phase : ClausePhase
  phase_in_support :
    match phase with
    | .init => conflict.support.init = true
    | .transit => conflict.support.transit = true
    | .terminal => conflict.support.terminal = true

/--
The exact material parity-mixing target.

The extractor is already structurally inhabited by fullConflictExtractor.
The remaining material content is:
  * two odd-separated orbit points with clause-supported observations,
  * equality of their clause phases,
  * a proof that this concrete equal-phase event projects to ObsEquiv.

No size/clock-only law can inhabit these fields.
-/
structure ClauseDerivedParityMixing
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i j : Nat
  odd_gap : OddGap i j
  obs_i :
    ClausePhaseObservation
      (complementToNTMCandidate M)
      (Orbit (R_M M hTotal) seed i)
      (M.timeBound (Orbit (R_M M hTotal) seed i).length)
  obs_j :
    ClausePhaseObservation
      (complementToNTMCandidate M)
      (Orbit (R_M M hTotal) seed j)
      (M.timeBound (Orbit (R_M M hTotal) seed j).length)
  same_phase : obs_i.phase = obs_j.phase
  phase_to_obs :
    obs_i.phase = obs_j.phase →
    ObsEquiv M
      (Orbit (R_M M hTotal) seed i)
      (Orbit (R_M M hTotal) seed j)

/--
Universal producer target for P03.  This proposition remains deliberately
uninhabited.
-/
def P03_MATERIAL_LAW : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (ClauseDerivedParityMixing M hTotal)

/-- Current fail-closed status. -/
def MATERIAL_GAPS : Nat := 1
def OPEN_BRIDGE : Nat := 1
def GREEN : Bool := false

#print axioms MCore.Real.P03MaterialLaw.supportedCNF_fullSupport

end P03MaterialLaw
end Real
end MCore
