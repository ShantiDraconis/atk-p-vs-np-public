import MCore.Real.P02OperatorKernel

namespace MCore
namespace Real
namespace P02FinalCompression

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel

/-- P01 is consumed explicitly as the canonical SAT-in-NP side.
This keeps the P02 kernel independent from legacy P01 implementation files. -/
abbrev P01Side : Prop :=
  SATInNPGap circuitBitEncoding

/-- A genuine P02 operator plus an explicit P01 side closes the
internal separation endpoint. -/
theorem canonical_p02_operator_closes
    (hP01 : P01Side)
    (P : CanonicalSATP02Producer) :
    PneqNP := by
  have hFail : UniversalFailure (SATBits circuitBitEncoding) :=
    (p02Producer_iff_universalFailure).mp ⟨P⟩
  exact target_failure_implies_p_ne_np hP01 hFail

/-- Exact final P02 residual, independent from any concrete P01 implementation. -/
abbrev FINAL_OPEN_MATH : Prop :=
  Nonempty CanonicalSATP02Producer

theorem final_open_math_iff_sat_not_in_p :
    FINAL_OPEN_MATH ↔
      ¬ InP (SATBits circuitBitEncoding) :=
  canonicalSATProducer_iff_notInP

theorem final_open_math_closes
    (hP01 : P01Side)
    (h : FINAL_OPEN_MATH) :
    PneqNP := by
  rcases h with ⟨P⟩
  exact canonical_p02_operator_closes hP01 P

end P02FinalCompression
end Real
end MCore
