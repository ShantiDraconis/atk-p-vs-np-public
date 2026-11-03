import MCore.Real.P01SourceCopyMachine
import MCore.Real.CanonicalSATParserMachine
import MCore.Real.P01WitnessPreservingPrep

namespace MCore
namespace Real
namespace P01SourceCopyHandoff

open CanonicalFinalProof
open P01SourceCopyMachine
open CanonicalSATParserMachine
open P01WitnessPreservingPrep

/-- Target post-copy layout: original source is preserved to the left of one
blank delimiter, and an exact copy begins under the head. -/
def copiedSourceLayout (source : BitString) : Tape (Option Bool) :=
  match source with
  | [] =>
      { left := [none], head := none, right := [] }
  | b :: bs =>
      { left := none :: source.reverse.map some,
        head := some b,
        right := bs.map some }

/-- Exact contract needed from the copy machine before parser composition. -/
structure SourceCopyCertificate where
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    forall source : BitString,
      sourceCopyMachine.HaltsWithin
        (timeBound source.length)
        (initialTMConfig sourceCopyMachine source)
  correct :
    forall source : BitString,
      (sourceCopyMachine.run
        (timeBound source.length)
        (initialTMConfig sourceCopyMachine source)).tape =
      copiedSourceLayout source

def SourceCopyGap : Prop := Nonempty SourceCopyCertificate

/-- The copied region presents the exact same visible bitstring from the head. -/
theorem copiedSourceLayout_visible
    (source : BitString) :
    CanonicalSATFrameAttack.tapeWord (copiedSourceLayout source) = source := by
  cases source <;>
    simp [copiedSourceLayout, CanonicalSATFrameAttack.tapeWord,
      CanonicalSATFrameAttack.readTapeCells]

/-- Parser correctness can therefore be reused semantically on the copied
visible word without changing the canonical source encoding. -/
theorem copied_visible_decode
    (source : BitString) :
    CanonicalCircuitBits.decodeCircuit
      (CanonicalSATFrameAttack.tapeWord (copiedSourceLayout source)) =
      CanonicalCircuitBits.decodeCircuit source := by
  rw [copiedSourceLayout_visible]

#print axioms MCore.Real.P01SourceCopyHandoff.copiedSourceLayout_visible
#print axioms MCore.Real.P01SourceCopyHandoff.copied_visible_decode

end P01SourceCopyHandoff
end Real
end MCore
