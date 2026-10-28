import MCore.BackwardAudit.OrientedWitnessBoundary

/-!
# Barrier audit for the restriction/potential route (C6–C12)

First instance of `SeparationTechniqueAudit`.  Each field is a recorded
classification of the route, not a theorem about it.  Nothing here proves
that the route fails or succeeds.
-/

namespace MCore
namespace BackwardAudit

/-- Barrier classification of the C6–C12 route: random restrictions, the
structural potential `Potential α β`, and the branching-cost payoff test on
`FormulaTree` (tree formulas, no gate sharing). -/
def restrictionPotentialRouteAudit : SeparationTechniqueAudit where
  relativization := .notAssessed
  naturalProofs := .appearsNatural
  algebrization := .notAssessed
  note :=
    "Natural Proofs (Razborov-Rudich): RISK, recorded as appearsNatural. " ++
    "Random-restriction lower bounds (Furst-Saxe-Sipser, Hastad) are the " ++
    "standard examples of natural proofs. If pseudorandom functions " ++
    "computable by polynomial-size formulas exist, no natural property " ++
    "proves super-polynomial formula lower bounds. Whether this route's " ++
    "property is both constructive and large has NOT been checked formally. " ++
    "Relativization / algebrization: notAssessed; both barriers are stated " ++
    "for uniform separations with oracles and do not apply directly to a " ++
    "non-uniform formula argument. Model scope: FormulaTree has no sharing, " ++
    "so the reachable conclusion is a formula-size bound (see " ++
    "MCore.C12.Calibration), not SAT not in P."

/-- The audit records no claimed escape from any barrier. -/
theorem restrictionPotentialRoute_claims_no_escape :
    restrictionPotentialRouteAudit.relativization ≠ .evidenceOfEscape ∧
    restrictionPotentialRouteAudit.naturalProofs ≠ .evidenceOfEscape ∧
    restrictionPotentialRouteAudit.algebrization ≠ .evidenceOfEscape := by
  decide

#print axioms MCore.BackwardAudit.restrictionPotentialRoute_claims_no_escape

end BackwardAudit
end MCore
