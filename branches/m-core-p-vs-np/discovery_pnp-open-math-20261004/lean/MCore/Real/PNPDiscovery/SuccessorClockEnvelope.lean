import MCore.Real.PNPDiscovery.OrbitLevelAlignmentCorrection
import MCore.Real.PNPDiscovery.EncodingDependencyMap
import MCore.Real.PNPNTMTableauClosure

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics
open PNPNTMTableauClosure
open PNPNTMTableauEncoding

/-- Exact quartic Cook--Levin output-length envelope already certified by the
concrete tableau producer. -/
def reductionLengthEnvelope
    (M : PolyDTMCandidate)
    (n : Nat) : Nat :=
  let N := complementToNTMCandidate M
  let t := M.timeBound n
  tableauEncodingCoeff N * (n + t + 1) ^ 4

/-- The real complemented reduction output is bounded by the certified
tableau quartic envelope. -/
theorem R_M_length_le_envelope
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    (R_M M hTotal x).length ≤
      reductionLengthEnvelope M x.length := by
  unfold reductionLengthEnvelope
  let N := complementToNTMCandidate M
  let t := M.timeBound x.length
  have h :=
    boundedExec_encoded_length_poly N x t
  unfold R_M complementSemanticReduction
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  simpa [N, t] using h

/-- Compose the candidate's stored polynomial clock with the concrete
Cook--Levin output-length envelope. -/
def successorClockEnvelope
    (M : PolyDTMCandidate)
    (n : Nat) : Nat :=
  (clockEnvelope M).coefficient *
    (reductionLengthEnvelope M n + 1) ^
      (clockEnvelope M).exponent

theorem successor_clock_le_envelope
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    M.timeBound (R_M M hTotal x).length ≤
      successorClockEnvelope M x.length := by
  have hClock :=
    timeBound_le_clockEnvelope M
      (R_M M hTotal x).length
  have hLen :=
    R_M_length_le_envelope M hTotal x
  unfold successorClockEnvelope
  exact Nat.le_trans hClock
    (Nat.mul_le_mul_left
      (clockEnvelope M).coefficient
      (Nat.pow_le_pow_left
        (by omega)
        (clockEnvelope M).exponent))

/-- Fully unfolded successor-clock bound. -/
theorem successor_clock_le_expanded
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    M.timeBound (R_M M hTotal x).length ≤
      (clockEnvelope M).coefficient *
        (tableauEncodingCoeff (complementToNTMCandidate M) *
          (x.length + M.timeBound x.length + 1) ^ 4 + 1) ^
        (clockEnvelope M).exponent := by
  simpa [successorClockEnvelope, reductionLengthEnvelope] using
    successor_clock_le_envelope M hTotal x

/-- Two-successor shared cone has an explicit common upper envelope whenever
the predecessor lengths coincide. -/
theorem successorSharedCone_le_of_length_eq
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (hLen : x.length = y.length) :
    SuccessorSharedReadConePrefix M hTotal x y ≤
      successorClockEnvelope M x.length + 1 := by
  unfold SuccessorSharedReadConePrefix SharedReadConePrefix
  have hx := successor_clock_le_envelope M hTotal x
  have hy := successor_clock_le_envelope M hTotal y
  rw [hLen] at hy
  omega

#print axioms MCore.Real.PNPDiscovery.R_M_length_le_envelope
#print axioms MCore.Real.PNPDiscovery.successor_clock_le_envelope
#print axioms MCore.Real.PNPDiscovery.successor_clock_le_expanded
#print axioms MCore.Real.PNPDiscovery.successorSharedCone_le_of_length_eq

end PNPDiscovery
end Real
end MCore
