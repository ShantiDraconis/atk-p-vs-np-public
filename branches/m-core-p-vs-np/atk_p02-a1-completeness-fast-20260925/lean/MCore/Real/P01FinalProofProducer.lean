import MCore.Real.P01ConstructionClose

namespace MCore
namespace Real
namespace P01FinalProofProducer

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P01ConstructionClose

/-- Minimal P01 producer for the final-proof clean lane.
No parser, research, audit, or alternate endpoint is imported here. -/
structure Producer where
  construction : P01MachineConstruction

def Producer.toGap (P : Producer) : P01ConstructionGap :=
  ⟨P.construction⟩

theorem Producer.toSATInNP
    (P : Producer) :
    SATInNPGap circuitBitEncoding :=
  construction_closes_p01 P.toGap

/-
Only remaining payload inside Producer.construction:
- stateCount
- machine
- blank_none
- timeBound
- time_poly
- halts
- accepts_iff
-/

#print axioms MCore.Real.P01FinalProofProducer.Producer.toSATInNP

end P01FinalProofProducer
end Real
end MCore
