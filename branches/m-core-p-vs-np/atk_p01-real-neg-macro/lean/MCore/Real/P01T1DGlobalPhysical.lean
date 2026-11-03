import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierReadWitnessLocal
import MCore.Real.P01FullVerifierEvalLocal
import MCore.Real.P01FullVerifierReverseDecoderGap
import MCore.Real.P01FullVerifierShuttleReturn

namespace MCore
namespace Real
namespace P01T1DGlobalPhysical

open P01FullVerifierPhysical
open P01FullVerifierReverseDecoderGap

/-- All converged local T1-D artifacts compile, but the remaining global
machine-level obligation is still the concrete PhysicalVerifierRealization. -/
def GlobalPhysicalVerifierGap : Prop :=
  Nonempty PhysicalVerifierRealization

theorem global_physical_gap_is_existing_gap :
    GlobalPhysicalVerifierGap = PhysicalVerifierGap := by
  rfl

/-- The reverse decoder remains a genuine prerequisite for any implementation
that follows the current scan/decode/evaluate architecture. No inhabitant is asserted. -/
def CurrentDecoderPrerequisite : Prop :=
  ReverseDecoderGap

#print axioms MCore.Real.P01T1DGlobalPhysical.global_physical_gap_is_existing_gap

end P01T1DGlobalPhysical
end Real
end MCore
