import MCore.Real.PNPDiscovery.EncodingDependencyMap
import MCore.Real.MachineRunLemmas
import MCore.Real.P02TotalCandidateKleeneReduction

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open MachineRunLemmas

/-- Canonical finitely-parameterized clock extracted from the stored
polynomial witness. -/
def canonicalClock
    (M : PolyDTMCandidate) : TimeBound :=
  fun n =>
    (clockEnvelope M).coefficient *
      (n + 1) ^ (clockEnvelope M).exponent

theorem timeBound_le_canonicalClock
    (M : PolyDTMCandidate)
    (n : Nat) :
    M.timeBound n ≤ canonicalClock M n :=
  timeBound_le_clockEnvelope M n

theorem canonicalClock_poly
    (M : PolyDTMCandidate) :
    PolynomialTimeBound (canonicalClock M) := by
  refine ⟨
    (clockEnvelope M).coefficient,
    (clockEnvelope M).exponent,
    ?_⟩
  intro n
  rfl

/-- Replace only the arbitrary function-valued clock by its canonical
polynomial envelope.  All finite machine data and acceptance semantics remain
unchanged. -/
noncomputable def canonicalClockCandidate
    (M : PolyDTMCandidate) :
    PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    timeBound := canonicalClock M
    time_poly := canonicalClock_poly M }

/-- Totality at the original declared clock implies totality at the larger
canonical envelope. -/
theorem canonicalClockCandidate_total
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    DeclaredClockTotal (canonicalClockCandidate M) := by
  intro x
  unfold DeclaredHalts
  change
    M.machine.HaltsWithin
      (canonicalClock M x.length)
      (initialTMConfig M.machine x)
  exact haltsWithin_mono
    M.machine
    (initialTMConfig M.machine x)
    (timeBound_le_canonicalClock M x.length)
    (hTotal x)

/-- Once the original run has halted, extending fuel to the canonical
polynomial envelope leaves the final configuration unchanged. -/
theorem canonicalClock_run_eq
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    M.machine.run
        (canonicalClock M x.length)
        (initialTMConfig M.machine x) =
      M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x) := by
  let cfg := initialTMConfig M.machine x
  let halted :=
    M.machine.run (M.timeBound x.length) cfg
  have hrun :
      M.machine.run (M.timeBound x.length) cfg = halted := rfl
  have hhalt :
      M.machine.halting halted.state = true := by
    exact hTotal x
  exact run_to_larger_fuel_of_halt
    M.machine cfg halted
    (timeBound_le_canonicalClock M x.length)
    hrun hhalt

/-- Declared acceptance is invariant under canonical clock normalization for
total candidates. -/
theorem canonicalClock_declaredAccepts_iff
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    DeclaredAccepts (canonicalClockCandidate M) x ↔
      DeclaredAccepts M x := by
  unfold DeclaredAccepts
  change
    M.accepting
        (M.machine.run
          (canonicalClock M x.length)
          (initialTMConfig M.machine x)).state = true ↔
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = true
  rw [canonicalClock_run_eq M hTotal x]

/-- CorrectAt is also preserved for any language once totality is known. -/
theorem canonicalClock_correctAt_iff
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (language : BitLanguage)
    (x : BitString) :
    (canonicalClockCandidate M).CorrectAt language x ↔
      M.CorrectAt language x := by
  unfold PolyDTMCandidate.CorrectAt
  change
    (M.machine.HaltsWithin
        (canonicalClock M x.length)
        (initialTMConfig M.machine x) ∧
      (DeclaredAccepts (canonicalClockCandidate M) x ↔ language x)) ↔
    (M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      (DeclaredAccepts M x ↔ language x))
  constructor
  · intro h
    exact ⟨hTotal x,
      (canonicalClock_declaredAccepts_iff M hTotal x).symm.trans h.2⟩
  · intro h
    exact ⟨canonicalClockCandidate_total M hTotal x,
      (canonicalClock_declaredAccepts_iff M hTotal x).trans h.2⟩

/-- Semantic reduction of the total-candidate universe:
for diagonal/self-reference purposes, arbitrary polynomially-bounded clock
functions may be replaced by finitely parameterized canonical polynomial
clocks without changing bounded acceptance. -/
structure CanonicalClockReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  normalized : PolyDTMCandidate := canonicalClockCandidate M
  total : DeclaredClockTotal normalized
  accepts :
    ∀ x : BitString,
      DeclaredAccepts normalized x ↔ DeclaredAccepts M x

noncomputable def canonicalClockReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    CanonicalClockReduction M hTotal :=
  { normalized := canonicalClockCandidate M
    total := canonicalClockCandidate_total M hTotal
    accepts := canonicalClock_declaredAccepts_iff M hTotal }

#print axioms MCore.Real.PNPDiscovery.canonicalClockCandidate_total
#print axioms MCore.Real.PNPDiscovery.canonicalClock_run_eq
#print axioms MCore.Real.PNPDiscovery.canonicalClock_declaredAccepts_iff
#print axioms MCore.Real.PNPDiscovery.canonicalClock_correctAt_iff

end PNPDiscovery
end Real
end MCore
