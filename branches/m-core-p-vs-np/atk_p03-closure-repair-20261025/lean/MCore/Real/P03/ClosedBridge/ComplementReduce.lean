import MCore.Real.P02ComplementRunRealization
import MCore.Real.P02TableauDynamics

namespace MCore.Real.P03.ClosedBridge.ComplementReduce

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics

theorem closed_complement_reduce
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    PNPCookLevinMaterialMinCut.CanonicalSAT (R_M M hTotal x) ↔
      ¬ DeclaredAccepts M x := by
  simpa [R_M] using complement_reduce_correct M hTotal x

#print axioms MCore.Real.P03.ClosedBridge.ComplementReduce.closed_complement_reduce

end MCore.Real.P03.ClosedBridge.ComplementReduce
