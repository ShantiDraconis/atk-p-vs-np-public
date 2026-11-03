import MCore.Real.P01ConstructionClose
import MCore.Real.P01IntegratedMachine
import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierPhysicalControl
import MCore.Real.P01ParserWitnessComposition
import MCore.Real.P01VerifierComposition

namespace MCore
namespace Real
namespace P01FastPathAttack

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P01ConstructionClose
open P01FullVerifierPhysical

/-- First hard implementation object on the shortest P01 path. -/
def P01PhysicalVerifierTarget : Prop :=
  Nonempty PhysicalVerifierRealization

/-- Final hard implementation object on the shortest P01 path. -/
def P01IntegratedConstructionTarget : Prop :=
  Nonempty P01MachineConstruction

theorem physical_target_closes_full_verifier
    (h : P01PhysicalVerifierTarget) :
    P01FullVerifierMachine.FullVerifierGap := by
  rcases h with ⟨R⟩
  exact physical_realization_closes_full_verifier R

theorem integrated_target_is_P01ConstructionGap :
    P01IntegratedConstructionTarget ↔ P01ConstructionGap :=
  Iff.rfl

theorem integrated_target_closes_P01
    (h : P01IntegratedConstructionTarget) :
    SATInNPGap circuitBitEncoding := by
  rcases h with ⟨C⟩
  exact integrated_construction_gives_sat_in_np C

/-
Shortest honest P01 route:

existing GREEN parser simulation
+ existing witness-preserving nondeterminism
+ existing verifier semantics
+ existing fixed integrated state layout
→ construct PhysicalVerifierRealization
→ construct one P01MachineConstruction
→ P01ConstructionGap
→ SATInNPGap.

No endpoint proposition is assumed here.
-/

#print axioms MCore.Real.P01FastPathAttack.physical_target_closes_full_verifier
#print axioms MCore.Real.P01FastPathAttack.integrated_target_closes_P01

end P01FastPathAttack
end Real
end MCore
