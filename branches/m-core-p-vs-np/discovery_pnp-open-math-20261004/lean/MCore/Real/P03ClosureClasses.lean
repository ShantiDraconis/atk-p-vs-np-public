import MCore.Real.P03OrbitalDeterministicSignature

namespace MCore
namespace Real
namespace P03ClosureClasses

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03InteractionConflict
open P03TransitionSignature
open P03OrbitalDeterministicSignature

abbrev UnsatCore
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :=
  ClauseUnsatCore M x t

abbrev Interaction
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :=
  OrbitalInteractionConflict M x t

abbrev TransitionOccurrence
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (core : ClauseUnsatCore M x t) :=
  TransitionClauseOccurrence M x t core

abbrev TransitionSignature
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (core : ClauseUnsatCore M x t) :=
  TransitionInteractionSignature M x t core

abbrev EffectSignature
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (core : ClauseUnsatCore M x t) :=
  ActiveEffectSignature M x t core

abbrev DeterministicSignature
    (candidate : PolyDTMCandidate) (x : BitString) (t : Nat)
    (core : ClauseUnsatCore (complementToNTMCandidate candidate) x t) :=
  DeterministicEffectSignature candidate x t core

abbrev OrbitalSignature
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (seed : BitString) :=
  OrbitalDeterministicEffectSignature candidate hTotal seed

end P03ClosureClasses
end Real
end MCore
