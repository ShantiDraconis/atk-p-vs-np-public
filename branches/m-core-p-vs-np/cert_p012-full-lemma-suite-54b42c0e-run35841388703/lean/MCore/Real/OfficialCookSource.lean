import MCore.Real.OfficialModel

namespace MCore
namespace Real
namespace OfficialCookSource

open OfficialModel

/-- Normative source record for the external P-vs-NP model target.
This is provenance only: it does not manufacture an OfficialComplexityModel
and does not prove model equivalence. -/
def cookCMISource : OfficialModelSource :=
  { statement :=
      "Stephen Cook, The P versus NP Problem: Section 1, pp. 1-2 defines P and NP and states the P versus NP problem."
    repository :=
      "Clay Mathematics Institute official problem description"
    namespaceName :=
      "External.CookCMI.PvsNP"
    sourceFile :=
      "pvsnp.pdf"
    closureCondition :=
      "A selected external model must be matched in both directions with the internal canonical deterministic and nondeterministic polynomial-time models, with explicit polynomial overhead and encoding normalization."
    statement_nonempty := by decide
    repository_nonempty := by decide
    namespace_nonempty := by decide
    sourceFile_nonempty := by decide
    closureCondition_nonempty := by decide }

/-- G3 provenance is no longer UNSET.  The mathematical model and bridge remain
separate open producers. -/
theorem cookCMISource_is_populated :
    cookCMISource.statement ≠ "" ∧
    cookCMISource.repository ≠ "" ∧
    cookCMISource.namespaceName ≠ "" ∧
    cookCMISource.sourceFile ≠ "" ∧
    cookCMISource.closureCondition ≠ "" := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

#print axioms MCore.Real.OfficialCookSource.cookCMISource_is_populated

end OfficialCookSource
end Real
end MCore
