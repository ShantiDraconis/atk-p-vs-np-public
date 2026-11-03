import MCore.Real.PNPDiscovery.SourceOffsetLowerEnvelope
import MCore.Real.PNPDiscovery.LengthSourceCompression

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Fully compressed necessary escape law for TerminalParityBarrier.
Every positive odd-separated orbit pair must either have different lengths,
or, at its canonical first source mismatch, satisfy the explicit
Cook--Levin-layout-vs-successor-clock inequality. -/
def BarrierArithmeticEscapeLaw
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat),
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length ∨
      ∃ hLen : x.length = y.length,
        let W :=
          barrierFirstSourceMismatchWitness
            M hTotal Hbar seed i d hLen
        sourceCellOffsetLowerEnvelope
            M x.length (M.timeBound x.length) W.j <
          successorSharedConeEnvelope M x y

theorem terminalParityBarrier_forces_arithmeticEscape
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    BarrierArithmeticEscapeLaw M hTotal := by
  intro Hbar seed i d
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  by_cases hLen : x.length = y.length
  · right
    refine ⟨hLen, ?_⟩
    exact barrier_equalLength_explicit_growth_constraint
      M hTotal Hbar seed i d hLen
  · exact Or.inl hLen

/-- The actual remaining mathematical obstruction after all current
decomposition.  To refute TerminalParityBarrier it suffices to find one odd
pair that escapes neither branch: same length and failure of the explicit
growth inequality. -/
def ArithmeticBarrierBreaker
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ Hbar : TerminalParityBarrier M hTotal,
    ∃ seed : BitString, ∃ i d : Nat,
      let x := orbit M hTotal seed (i + 1)
      let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
      ∃ hLen : x.length = y.length,
        let W :=
          barrierFirstSourceMismatchWitness
            M hTotal Hbar seed i d hLen
        successorSharedConeEnvelope M x y ≤
          sourceCellOffsetLowerEnvelope
            M x.length (M.timeBound x.length) W.j

/-- An arithmetic breaker contradicts the necessary escape law and therefore
kills the terminal parity barrier. -/
theorem arithmeticBarrierBreaker_kills_barrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (B : ArithmeticBarrierBreaker M hTotal) :
    ¬ TerminalParityBarrier M hTotal := by
  intro Hbar
  rcases B Hbar with ⟨seed, i, d, hLen, hBreak⟩
  have hNeed :=
    barrier_equalLength_explicit_growth_constraint
      M hTotal Hbar seed i d hLen
  omega

/-- Uniform remaining producer at the current depth. -/
def ArithmeticBarrierBreakerProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ArithmeticBarrierBreaker M hTotal

#print axioms MCore.Real.PNPDiscovery.terminalParityBarrier_forces_arithmeticEscape
#print axioms MCore.Real.PNPDiscovery.arithmeticBarrierBreaker_kills_barrier

end PNPDiscovery
end Real
end MCore
