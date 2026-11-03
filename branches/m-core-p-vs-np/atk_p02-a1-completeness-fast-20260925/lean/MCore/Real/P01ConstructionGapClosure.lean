import MCore.Real.P01ConstructionClose
import MCore.Real.P01WitnessIndexedReadProof
import MCore.Real.P01FullVerifierPhysical

namespace MCore
namespace Real
namespace P01ConstructionGapClosure

open CanonicalFinalProof
open P01FinalCertificate
open P01ConstructionClose

/-- Exact closure contract for P01 on the active lane. -/
structure P01ClosureData where
  construction : P01MachineConstruction

def P01ClosureData.toGap (D : P01ClosureData) : P01ConstructionGap :=
  ⟨D.construction⟩

theorem P01ClosureData.closes
    (D : P01ClosureData) :
    CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 D.toGap

/-
Required for a real inhabitant of P01MachineConstruction:
1. stateCount derived from the actual composed finite control.
2. machine implementing parser -> witness -> verifier -> halt.
3. blank_none for the canonical blank none.
4. timeBound from the real composed execution.
5. time_poly.
6. halts for every BitString.
7. accepts_iff SATBits for every BitString.

Reusable active-lane inputs include parser/verifier composition and
P01WitnessIndexedRead*. They do not themselves inhabit the terminal construction.
-/

#print axioms MCore.Real.P01ConstructionGapClosure.P01ClosureData.closes

end P01ConstructionGapClosure
end Real
end MCore
