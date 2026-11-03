import MCore.Real.P03TransitionSignature
import MCore.Real.P03Lemmas

namespace MCore
namespace Real
namespace P03OrbitalDeterministicSignature

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03InteractionConflict
open P03TransitionSignature
open P03Lemmas

/--
An outer Cook--Levin orbit point together with one internal deterministic
transition-effect signature from the tableau generated at that orbit point.

outerIndex is the iteration number k of R^k(seed).
internalStep is the machine time inside the tableau for R^k(seed).
They are intentionally distinct coordinates.
-/
structure OrbitalDeterministicEffectSignature
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (seed : BitString) where
  outerIndex : Nat
  source : BitString :=
    Orbit (R_M candidate hTotal) seed outerIndex
  clock : Nat :=
    candidate.timeBound source.length
  core :
    ClauseUnsatCore
      (complementToNTMCandidate candidate)
      source
      clock
  effect :
    DeterministicEffectSignature
      candidate source clock core

/--
The next outer orbit point decodes back to this signature's source point.
This says nothing yet about the internal control state or tape symbol.
-/
theorem orbital_signature_decodes_source
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (seed : BitString)
    (sig :
      OrbitalDeterministicEffectSignature candidate hTotal seed) :
    decodeSourceBits
        (complementToNTMCandidate candidate)
        sig.source.length
        (candidate.timeBound sig.source.length)
        (Orbit (R_M candidate hTotal) seed (sig.outerIndex + 1)) =
      some sig.source := by
  simpa [OrbitalDeterministicEffectSignature.source] using
    (decode_recovers_orbit_step
      candidate hTotal seed sig.outerIndex)

/--
Internal transition time remains bounded by the tableau clock; it is not the
outer orbit index.
-/
theorem internal_step_lt_clock
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (seed : BitString)
    (sig :
      OrbitalDeterministicEffectSignature candidate hTotal seed) :
    sig.effect.effect.base.step < sig.clock :=
  sig.effect.effect.base.step_lt

#print axioms MCore.Real.P03OrbitalDeterministicSignature.orbital_signature_decodes_source
#print axioms MCore.Real.P03OrbitalDeterministicSignature.internal_step_lt_clock

end P03OrbitalDeterministicSignature
end Real
end MCore
