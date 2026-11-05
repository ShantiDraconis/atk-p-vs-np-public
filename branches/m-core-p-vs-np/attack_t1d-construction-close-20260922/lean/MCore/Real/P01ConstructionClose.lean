import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01ConstructionClose

open CanonicalSATNTMAttack
open P01FinalCertificate

/-- Exact T1.D target; no weakening or alternate endpoint is introduced. -/
abbrev T1DTarget : Prop := P01ConstructionGap

/-- Once the concrete construction exists, the existing certified promotion
closes P01.  This theorem adds no endpoint premise beyond T1DTarget itself. -/
theorem t1d_promotes
    (h : T1DTarget) :
    CanonicalSATMachineClosure :=
  construction_closes_p01 h

#print axioms MCore.Real.P01ConstructionClose.t1d_promotes

end P01ConstructionClose
end Real
end MCore
