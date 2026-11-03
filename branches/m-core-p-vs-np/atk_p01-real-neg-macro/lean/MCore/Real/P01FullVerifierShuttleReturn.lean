import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierShuttleReturn

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalShuttles

theorem execMoves_append {Symbol : Type}
    (blank : Symbol) (xs ys : List Direction) (t : Tape Symbol) :
    execMoves blank (xs ++ ys) t =
      execMoves blank ys (execMoves blank xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons d ds ih =>
      simp [execMoves, ih]

theorem witness_roundTrip_exec
    (witness source : CanonicalFinalProof.BitString) (i : Nat) :
    execMoves (none : Option Bool)
      (moveToWitnessSeq source i ++ moveToStackSeq source i)
      (sourceEndTape witness source) =
    execMoves (none : Option Bool) (moveToStackSeq source i)
      (execMoves (none : Option Bool) (moveToWitnessSeq source i)
        (sourceEndTape witness source)) := by
  exact execMoves_append (none : Option Bool) _ _ _

#print axioms MCore.Real.P01FullVerifierShuttleReturn.execMoves_append
#print axioms MCore.Real.P01FullVerifierShuttleReturn.witness_roundTrip_exec

end P01FullVerifierShuttleReturn
end Real
end MCore
