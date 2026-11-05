import MCore.Signature
import MCore.Boundary
namespace MCore
theorem candidate_ne_provedProperty : SignatureStatus.candidate ≠ SignatureStatus.provedProperty := by decide
theorem boundary_ne_regular : BoundaryPhase.boundary ≠ BoundaryPhase.regular := by decide
end MCore
