import MCore.Real.P02EqualityCompositionUnified

namespace MCore
namespace Real
namespace P02TerminalForcingSAT

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Fully explicit data required for a material SAT solver in the canonical model. -/
structure SATSolverData where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ x : BitString,
      machine.HaltsWithin
        (timeBound x.length)
        (initialTMConfig machine x)
  correct :
    ∀ x : BitString,
      (accepting
          (machine.run
            (timeBound x.length)
            (initialTMConfig machine x)).state = true) ↔
        P02EqualityBranchMaterialFrontier.CanonicalSAT x

/-- No wrapper is hidden here: the explicit fields assemble exactly a
PolyDTMRealization of canonical SAT. -/
def SATSolverData.toRealization
    (S : SATSolverData) :
    PolyDTMRealization P02EqualityBranchMaterialFrontier.CanonicalSAT :=
  { candidate :=
      { stateCount := S.stateCount
        machine := S.machine
        blank_none := S.blank_none
        accepting := S.accepting
        timeBound := S.timeBound
        time_poly := S.time_poly }
    decides := by
      intro x
      exact ⟨S.halts x, S.correct x⟩ }

/-- Exact terminal equality obligation, fully expanded into physical solver data. -/
def SAT_SOLVER_TERMINAL : Prop :=
  Nonempty SATSolverData

theorem satSolverData_iff_realization :
    SAT_SOLVER_TERMINAL ↔
      Nonempty (PolyDTMRealization
        P02EqualityBranchMaterialFrontier.CanonicalSAT) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toRealization⟩
  · rintro ⟨R⟩
    refine ⟨{
      stateCount := R.candidate.stateCount
      machine := R.candidate.machine
      blank_none := R.candidate.blank_none
      accepting := R.candidate.accepting
      timeBound := R.candidate.timeBound
      time_poly := R.candidate.time_poly
      halts := ?_
      correct := ?_ }⟩
    · intro x
      exact (R.decides x).1
    · intro x
      exact (R.decides x).2

/-- The requested terminal object name. It can only be defined from actual
material SAT solver data; no SAT-in-P assumption is inserted here. -/
def satSolverOfData
    (S : SATSolverData) :
    PolyDTMRealization P02EqualityBranchMaterialFrontier.CanonicalSAT :=
  S.toRealization

#print axioms MCore.Real.P02TerminalForcingSAT.SATSolverData.toRealization
#print axioms MCore.Real.P02TerminalForcingSAT.satSolverData_iff_realization
#print axioms MCore.Real.P02TerminalForcingSAT.satSolverOfData

end P02TerminalForcingSAT
end Real
end MCore
