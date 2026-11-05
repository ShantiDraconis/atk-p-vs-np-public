import MCore.Real.P01RawDecodeFailureCases
import MCore.Real.P01RawMalformedBaseProducer
import MCore.Real.P01RawMalformedRecursiveLeft
import MCore.Real.P01RawMalformedRecursiveRight

namespace MCore
namespace Real
namespace P01RawMalformedProducer

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01EncodedStackEvaluator
open P01CheckedVerifierInvariant
open P01RawTotalContract
open P01RawDecodeFailureCases
open P01RawMalformedBaseProducer
open P01RawMalformedRecursiveLeft
open P01RawMalformedRecursiveRight

/-- The complete sufficient-fuel raw decoder failure producer.

The induction follows the actual recursive decoder:
* short/invalid/unary failures use the certified base machines;
* NOT/AND-left/OR-left push one continuation and recurse;
* AND-right/OR-right evaluate the valid left prefix with the exact circuit
  producer, perform the certified continuation handoff, then recurse.

No endpoint proposition or parser oracle appears. -/
theorem rawMalformedPhysicalProducer :
    RawMalformedPhysicalProducer := by
  intro fuel
  induction fuel with
  | zero =>
      intro witness bits frames mode consumed padding n
        hFuel hNone hLayout hWitness
      omega
  | succ f ih =>
      intro witness bits frames mode consumed padding n
        hFuel hNone hLayout hWitness
      have hcase :=
        decodeCircuitCore_none_cases (f + 1) bits hNone
      cases hcase with
      | fuelZero bits =>
          omega
      | short f' bits hshort =>
          exact short_reaches_fail_closed
            witness bits (encodeEvalFrames frames)
            mode consumed padding n (f + 1)
            hshort hLayout
      | invalid110 f' rest =>
          exact invalid_tag_reaches_fail_closed
            witness rest (encodeEvalFrames frames)
            mode consumed padding n (f + 1)
            false (Or.inl rfl) hLayout
      | invalid111 f' rest =>
          exact invalid_tag_reaches_fail_closed
            witness rest (encodeEvalFrames frames)
            mode consumed padding n (f + 1)
            true (Or.inr rfl) hLayout
      | inputUnary f' rest hdec =>
          have hshape := inputUnary_payload_all_true hdec
          have hLayout' :
              CheckedLayoutBound n consumed
                (false :: false :: false ::
                  List.replicate rest.length true)
                (encodeEvalFrames frames) := by
            simpa [hshape] using hLayout
          have h :=
            unary_reaches_fail_closed
              witness (encodeEvalFrames frames)
              mode consumed padding n (f + 1) rest.length hLayout'
          simpa [hshape] using h
      | negChild f' rest hchild =>
          exact neg_child_failure
            f n consumed padding witness rest frames mode ih
            (by simpa using hFuel) hchild
            (by simpa using hLayout)
            (by simpa using hWitness)
      | andLeft f' rest hleft =>
          exact and_left_failure
            f n consumed padding witness rest frames mode ih
            (by simpa using hFuel) hleft
            (by simpa using hLayout)
            (by simpa using hWitness)
      | andRight f' rest rest' left hleft hright =>
          exact and_right_failure
            f n consumed padding witness rest rest'
            frames mode left ih
            (by simpa using hFuel)
            hleft hright
            (by simpa using hLayout)
            (by simpa using hWitness)
      | orLeft f' rest hleft =>
          exact or_left_failure
            f n consumed padding witness rest frames mode ih
            (by simpa using hFuel) hleft
            (by simpa using hLayout)
            (by simpa using hWitness)
      | orRight f' rest rest' left hleft hright =>
          exact or_right_failure
            f n consumed padding witness rest rest'
            frames mode left ih
            (by simpa using hFuel)
            hleft hright
            (by simpa using hLayout)
            (by simpa using hWitness)

/-- Kernel object packaging the complete raw malformed recursion. -/
def rawTotalKernel : RawTotalKernel where
  malformed := rawMalformedPhysicalProducer

#print axioms MCore.Real.P01RawMalformedProducer.rawMalformedPhysicalProducer
#print axioms MCore.Real.P01RawMalformedProducer.rawTotalKernel

end P01RawMalformedProducer
end Real
end MCore
