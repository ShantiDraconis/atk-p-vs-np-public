import MCore.Real.PNPDiscovery.FirstGlobalBreak
import MCore.Real.PNPDiscovery.SuccessorClockEnvelope
import MCore.Real.PNPDiscovery.EncodingSpine

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics

/-- Explicit upper envelope for the shared successor read cone. -/
def successorSharedConeEnvelope
    (M : PolyDTMCandidate)
    (x y : BitString) : Nat :=
  Nat.min
    (successorClockEnvelope M x.length)
    (successorClockEnvelope M y.length) + 1

theorem successorSharedCone_le_envelope
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString) :
    SuccessorSharedReadConePrefix M hTotal x y ≤
      successorSharedConeEnvelope M x y := by
  unfold SuccessorSharedReadConePrefix
  unfold SharedReadConePrefix
  unfold successorSharedConeEnvelope
  have hx := successor_clock_le_envelope M hTotal x
  have hy := successor_clock_le_envelope M hTotal y
  omega

/-- Any two real reduction outputs agree through the entire candidate-only
initial-state encoding prefix. -/
theorem R_outputs_agree_initialStatePrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString) :
    (R_M M hTotal x).take
        (initialStateEncodingPrefix M).length =
      (R_M M hTotal y).take
        (initialStateEncodingPrefix M).length := by
  exact stablePrefix_initialStateBlock M hTotal x y

/-- Therefore an unequal pair of real reduction outputs cannot have its first
prefix break at or before the certified stable initial-state block. -/
theorem firstBreak_after_initialStatePrefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (hne : R_M M hTotal x ≠ R_M M hTotal y) :
    (initialStateEncodingPrefix M).length <
      firstPrefixBreak
        (R_M M hTotal x)
        (R_M M hTotal y)
        hne := by
  by_contra hNot
  have hle :
      firstPrefixBreak
          (R_M M hTotal x)
          (R_M M hTotal y)
          hne ≤
        (initialStateEncodingPrefix M).length := by
    omega
  have hBreak :=
    firstPrefixBreak_spec
      (R_M M hTotal x)
      (R_M M hTotal y)
      hne
  have hStable :=
    R_outputs_agree_initialStatePrefix M hTotal x y
  have hTake := congrArg
    (fun bs : BitString =>
      bs.take
        (firstPrefixBreak
          (R_M M hTotal x)
          (R_M M hTotal y)
          hne))
    hStable
  have hEq :
      (R_M M hTotal x).take
          (firstPrefixBreak
            (R_M M hTotal x)
            (R_M M hTotal y)
            hne) =
        (R_M M hTotal y).take
          (firstPrefixBreak
            (R_M M hTotal x)
            (R_M M hTotal y)
            hne) := by
    simpa [List.take_take, Nat.min_eq_left hle] using hTake
  exact hBreak hEq

/-- Quantitative sandwich forced by TerminalParityBarrier.
The first global break of each odd successor pair is trapped strictly after
the fixed structural state prefix and at/before an explicit polynomial clock
envelope. -/
theorem barrier_firstBreak_sandwich
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    (initialStateEncodingPrefix M).length <
      successorFirstPrefixBreak M hTotal Hbar seed i d ∧
    successorFirstPrefixBreak M hTotal Hbar seed i d ≤
      successorSharedConeEnvelope M x y := by
  dsimp
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  have hne :=
    barrier_successors_ne M hTotal Hbar seed i d
  constructor
  · simpa [successorFirstPrefixBreak, x, y] using
      firstBreak_after_initialStatePrefix
        M hTotal x y hne
  · exact Nat.le_trans
      (barrier_firstGlobalBreak_visible
        M hTotal Hbar seed i d)
      (successorSharedCone_le_envelope
        M hTotal x y)

/-- Pure arithmetic impossibility criterion:
if the certified stable prefix reaches the successor cone envelope for one odd
pair, TerminalParityBarrier is impossible. -/
theorem stablePrefix_reaches_envelope_kills_barrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat)
    (hDom :
      successorSharedConeEnvelope M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) ≤
      (initialStateEncodingPrefix M).length) :
    False := by
  have h :=
    barrier_firstBreak_sandwich M hTotal Hbar seed i d
  omega

#print axioms MCore.Real.PNPDiscovery.successorSharedCone_le_envelope
#print axioms MCore.Real.PNPDiscovery.firstBreak_after_initialStatePrefix
#print axioms MCore.Real.PNPDiscovery.barrier_firstBreak_sandwich
#print axioms MCore.Real.PNPDiscovery.stablePrefix_reaches_envelope_kills_barrier

end PNPDiscovery
end Real
end MCore
