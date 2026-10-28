import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierReadWitnessLocal

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalShuttles

def physicalWitnessRead
    (witness source : BitString) (i : Nat) : Option Bool :=
  (execMoves none (moveToWitnessSeq source i)
    (sourceEndTape witness source)).head

theorem physicalWitnessRead_correct
    (witness source : BitString) (i : Nat) (hi : i < witness.length) :
    physicalWitnessRead witness source i = some witness[i] := by
  exact moveToWitnessSeq_head_correct witness source i hi

#print axioms MCore.Real.P01FullVerifierReadWitnessLocal.physicalWitnessRead_correct

end P01FullVerifierReadWitnessLocal
end Real
end MCore
