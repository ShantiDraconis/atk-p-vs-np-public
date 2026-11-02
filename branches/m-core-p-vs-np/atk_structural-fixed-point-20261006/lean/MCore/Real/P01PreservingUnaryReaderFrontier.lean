import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.P01FinalCertificate
import MCore.Real.MachineRunLemmas
import MCore.Real.P01PreservingUnaryPhysicalRuns

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate

/-!
Exact material frontier for the universal preserving unary reader.

This file intentionally contains definitions of the remaining proposition
shapes only. It introduces no unproved declaration, theorem-by-decree, or external
closure claim.
-/

/-- One successor unary marker must advance the preserving machine from one
canonical loop configuration to the next while extending the traversed prefix
by exactly the next witness bit. -/
def SuccessorCycleObligation : Prop :=
  ∀ (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat),
    pref ≠ [] →
    ∃ steps : Nat,
      steps ≤ (pref.length + n + suffix.length + 1)^2 + 16 ∧
      preservingUnaryReadMachine.run steps
          (indexSomeConfig pref (b :: suffix) (n + 1)) =
        indexSomeConfig (pref ++ [b]) suffix n

/-- Exact candidate cost of one reachable successor cycle.  The physical
execution proof is the remaining content; this arithmetic lemma discharges
the frontier's polynomial budget once that equality is established. -/
def successorCycleSteps (pref : BitString) : Nat :=
  4 * pref.length + 8

theorem successorCycleSteps_bound
    (pref suffix : BitString) (n : Nat)
    (hpref : pref ≠ []) :
    successorCycleSteps pref ≤
      (pref.length + n + suffix.length + 1)^2 + 16 := by
  have hlen : 1 ≤ pref.length := by
    cases pref with
    | nil => contradiction
    | cons _ xs => simp
  let m := pref.length + n + suffix.length + 1
  have hpm : pref.length ≤ m := by
    dsimp [m]
    omega
  have hm2 : 2 ≤ m := by
    dsimp [m]
    omega
  have h4pm : 4 * pref.length ≤ 4 * m :=
    Nat.mul_le_mul_left 4 hpm
  have hquad : 4 * m ≤ m ^ 2 + 8 := by
    by_cases h4 : 4 ≤ m
    · have hmul : 4 * m ≤ m * m :=
        Nat.mul_le_mul_right m h4
      simpa [Nat.pow_two] using
        Nat.le_trans hmul (Nat.le_add_right (m * m) 8)
    · have hm_cases : m = 2 ∨ m = 3 := by omega
      rcases hm_cases with hm | hm
      · simp [hm]
      · simp [hm]
  unfold successorCycleSteps
  dsimp [m] at h4pm hquad ⊢
  omega

/-- Physical equality still to be proved against the real transition graph.
Keeping it separate prevents the polynomial side condition from obscuring the
only remaining machine-level obligation. -/
def SuccessorCyclePhysicalEquality : Prop :=
  ∀ (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat),
    pref ≠ [] →
    preservingUnaryReadMachine.run (successorCycleSteps pref)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      indexSomeConfig (pref ++ [b]) suffix n

theorem successorCyclePhysicalEquality_closes_frontier
    (hphys : SuccessorCyclePhysicalEquality) :
    SuccessorCycleObligation := by
  intro pref b suffix n hpref
  refine ⟨successorCycleSteps pref,
    successorCycleSteps_bound pref suffix n hpref, ?_⟩
  exact hphys pref b suffix n hpref

theorem successorCyclePhysicalEquality_material :
    SuccessorCyclePhysicalEquality := by
  intro pref b suffix n hpref
  exact
    P01PreservingUnaryPhysicalRuns.indexSome_run_advance
      pref b suffix n hpref

theorem successorCycleObligation_material :
    SuccessorCycleObligation :=
  successorCyclePhysicalEquality_closes_frontier
    successorCyclePhysicalEquality_material

#print axioms MCore.Real.P01PreservingUnaryReaderFrontier.successorCycleSteps_bound
#print axioms MCore.Real.P01PreservingUnaryReaderFrontier.successorCyclePhysicalEquality_closes_frontier
#print axioms MCore.Real.P01PreservingUnaryReaderFrontier.successorCyclePhysicalEquality_material
#print axioms MCore.Real.P01PreservingUnaryReaderFrontier.successorCycleObligation_material

/-- The terminal target remains the existing universal material contract. -/
def UniversalReaderMaterialTarget : Prop :=
  PreservingUnaryReaderGap

/-- P01 integration may advance only after the universal reader is inhabited. -/
def ReaderBeforeP01Construction : Prop :=
  PreservingUnaryReaderGap → P01FinalCertificate.P01ConstructionGap

end P01PreservingUnaryReaderFrontier
end Real
end MCore
