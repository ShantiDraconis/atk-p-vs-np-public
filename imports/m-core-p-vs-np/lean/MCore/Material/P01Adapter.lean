import MCore.Material.Closure
import MCore.Real.P01FinalCertificate
namespace MCore.Material
open MCore.Real.P01FinalCertificate

def P01CanonicalMaterial : Prop := P01ConstructionGap

theorem p01_material_closes_sat_machine (h : P01CanonicalMaterial) :
    MCore.Real.CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 h

end MCore.Material
