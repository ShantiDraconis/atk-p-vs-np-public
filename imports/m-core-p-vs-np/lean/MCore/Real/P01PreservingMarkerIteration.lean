import MCore.Real.P01InputNodePreservingPlan

namespace MCore
namespace Real
namespace P01PreservingMarkerIteration

open CanonicalFinalProof
open P01InputNodePreservingPlan

/-!
# Iterated reversible marker law

This is the algebraic induction needed by the physical unary driver.  It does
not invent a new producer: it proves that repeated local marker advances and
rewinds preserve the represented witness payload for an arbitrary finite
pref.
-/

def splitPayload (pref suffix : BitString) : BitString :=
  pref ++ suffix

def advanceSpec : BitString → BitString → BitString × BitString
  | pref, [] => (pref, [])
  | pref, b :: suffix => (pref ++ [b], suffix)

def advanceN : Nat → BitString → BitString → BitString × BitString
  | 0, pref, suffix => (pref, suffix)
  | n + 1, pref, suffix =>
      let p := advanceSpec pref suffix
      advanceN n p.1 p.2

theorem advanceSpec_payload
    (pref suffix : BitString) :
    let p := advanceSpec pref suffix
    splitPayload p.1 p.2 = splitPayload pref suffix := by
  cases suffix with
  | nil =>
      simp [advanceSpec, splitPayload]
  | cons b bs =>
      simp [advanceSpec, splitPayload, List.append_assoc]

theorem advanceN_payload
    (n : Nat) (pref suffix : BitString) :
    let p := advanceN n pref suffix
    splitPayload p.1 p.2 = splitPayload pref suffix := by
  induction n generalizing pref suffix with
  | zero =>
      simp [advanceN, splitPayload]
  | succ n ih =>
      simp only [advanceN]
      let p := advanceSpec pref suffix
      have hstep : splitPayload p.1 p.2 = splitPayload pref suffix :=
        advanceSpec_payload pref suffix
      have hrest := ih p.1 p.2
      simpa [p] using hrest.trans hstep

theorem advanceN_zero
    (pref suffix : BitString) :
    advanceN 0 pref suffix = (pref, suffix) := rfl

/-- If n is within the suffix length, n logical marker advances expose the nth
cell as the head of the remaining suffix while preserving the total payload. -/
theorem advanceN_exposes_getD
    (n : Nat) (pref suffix : BitString)
    (h : n < suffix.length) :
    ∃ pref' b tail,
      advanceN n pref suffix = (pref', b :: tail) ∧
      splitPayload pref' (b :: tail) = splitPayload pref suffix ∧
      b = suffix.getD n false := by
  induction n generalizing pref suffix with
  | zero =>
      cases suffix with
      | nil =>
          simp at h
      | cons b tail =>
          refine ⟨pref, b, tail, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · simp [List.getD_cons_zero]
  | succ n ih =>
      cases suffix with
      | nil =>
          simp at h
      | cons b tail =>
          have ht : n < tail.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          have hih := ih (pref := pref ++ [b]) (suffix := tail) ht
          rcases hih with ⟨pref', c, rest, hrun, hpayload, hget⟩
          refine ⟨pref', c, rest, ?_, ?_, ?_⟩
          · simpa [advanceN, advanceSpec] using hrun
          · have hstep :
                splitPayload (pref ++ [b]) tail =
                  splitPayload pref (b :: tail) := by
                simp [splitPayload, List.append_assoc]
            exact hpayload.trans hstep
          · simpa [List.getD_cons_succ] using hget

/-- A full logical rewind is simply restoration to the original split.  The
physical inverse for each cell is markerRewind_layout. -/
def rewindSpec (originalPrefix originalSuffix : BitString) :
    BitString × BitString :=
  (originalPrefix, originalSuffix)

theorem advance_then_rewind_payload
    (n : Nat) (pref suffix : BitString) :
    let p := advanceN n pref suffix
    splitPayload (rewindSpec pref suffix).1
      (rewindSpec pref suffix).2 =
    splitPayload p.1 p.2 := by
  have h := advanceN_payload n pref suffix
  simpa [rewindSpec] using h.symm

#print axioms MCore.Real.P01PreservingMarkerIteration.advanceN_payload
#print axioms MCore.Real.P01PreservingMarkerIteration.advanceN_exposes_getD
#print axioms MCore.Real.P01PreservingMarkerIteration.advance_then_rewind_payload

end P01PreservingMarkerIteration
end Real
end MCore
