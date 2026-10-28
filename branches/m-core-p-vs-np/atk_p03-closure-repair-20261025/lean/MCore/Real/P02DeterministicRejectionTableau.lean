import MCore.Real.PNPNTMTableauEncoding
import MCore.Real.CanonicalPSubsetNP

namespace MCore
namespace Real
namespace P02DeterministicRejectionTableau

-- Dedicated kernel gate trigger; semantics unchanged.

open CanonicalFinalProof
open CanonicalPSubsetNP
open PNPNTMTableauEncoding
open CircuitK1
open CanonicalCircuitBits

/-- Deterministic embedding with terminal labels swapped.
Transitions and stopping states are unchanged; only accept/reject meaning flips. -/
def complementToNTM
    (M : PolyDTMCandidate) :
    NTM (Fin (M.stateCount + 1)) (Option Bool) :=
  let B := CanonicalPSubsetNP.toNTM M
  { initial := B.initial
    blank := B.blank
    transition := B.transition
    accepting := B.rejecting
    rejecting := B.accepting }

theorem complement_accept_or_reject_eq_halting
    (M : PolyDTMCandidate)
    (q : Fin (M.stateCount + 1)) :
    ((complementToNTM M).accepting q ||
      (complementToNTM M).rejecting q) =
      M.machine.halting q := by
  cases h : M.machine.halting q <;>
    cases a : M.accepting q <;>
    simp [complementToNTM, CanonicalPSubsetNP.toNTM, h, a]

theorem complement_successors_to_tm
    (M : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (M.stateCount + 1))
        (Option Bool)) :
    (complementToNTM M).successors config =
      [M.machine.step config] := by
  rfl

def complementCandidate
    (M : PolyDTMCandidate) :
    PolyNTMCandidate :=
  { stateCount := M.stateCount
    machine := complementToNTM M
    blank_none := M.blank_none
    timeBound := M.timeBound
    time_poly := M.time_poly }

theorem complement_runBranches_to_tm_run
    (M : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration
        (Fin (M.stateCount + 1))
        (Option Bool)) :
    (complementToNTM M).runBranches fuel [config] =
      [M.machine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ n ih =>
      by_cases h : M.machine.halting config.state = true
      · have hstop :
          ((complementToNTM M).accepting config.state ||
            (complementToNTM M).rejecting config.state) = true := by
          rw [complement_accept_or_reject_eq_halting]
          exact h
        have hHalted :
            [config].filter (fun c =>
              (complementToNTM M).accepting c.state ||
                (complementToNTM M).rejecting c.state) = [config] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((complementToNTM M).accepting config.state ||
                (complementToNTM M).rejecting config.state) = false := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((complementToNTM M).accepting c.state ||
                (complementToNTM M).rejecting c.state)) = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (complementToNTM M).runBranches (n + 1) [config]
              = (complementToNTM M).runBranches n [config] := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = [M.machine.run n config] := ih config
          _ = [config] := by
                rw [CanonicalPSubsetNP.tm_run_of_halted M config h n]
          _ = [M.machine.run (n + 1) config] := by
                simp [TM.run, h]
      · have hFalse : M.machine.halting config.state = false := by
          cases hval : M.machine.halting config.state <;> simp_all
        have hstop :
          ((complementToNTM M).accepting config.state ||
            (complementToNTM M).rejecting config.state) = false := by
          rw [complement_accept_or_reject_eq_halting]
          exact hFalse
        have hHalted :
            [config].filter (fun c =>
              (complementToNTM M).accepting c.state ||
                (complementToNTM M).rejecting c.state) = [] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((complementToNTM M).accepting config.state ||
                (complementToNTM M).rejecting config.state) = true := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((complementToNTM M).accepting c.state ||
                (complementToNTM M).rejecting c.state)) = [config] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (complementToNTM M).runBranches (n + 1) [config]
              = (complementToNTM M).runBranches n
                  ((complementToNTM M).successors config) := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = (complementToNTM M).runBranches n
                  [M.machine.step config] := by
                rw [complement_successors_to_tm]
          _ = [M.machine.run n (M.machine.step config)] :=
                ih (M.machine.step config)
          _ = [M.machine.run (n + 1) config] := by
                simp [TM.run, h]

theorem complement_acceptsWithin_iff_rejects_at_fuel
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    (complementToNTM M).AcceptsWithin t
        (initialNTMConfig (complementToNTM M) x) ↔
      M.machine.HaltsWithin t (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run t (initialTMConfig M.machine x)).state = false := by
  rw [show initialNTMConfig (complementToNTM M) x =
      initialTMConfig M.machine x by rfl]
  constructor
  · rintro ⟨reached, hmem, hacc⟩
    rw [complement_runBranches_to_tm_run M t
      (initialTMConfig M.machine x)] at hmem
    have hreached :
        reached = M.machine.run t (initialTMConfig M.machine x) := by
      simpa using hmem
    subst reached
    have hacc' :
        Bool.and
          (M.machine.halting
            (M.machine.run t (initialTMConfig M.machine x)).state)
          (!(M.accepting
            (M.machine.run t (initialTMConfig M.machine x)).state)) = true := by
      simpa [complementToNTM, CanonicalPSubsetNP.toNTM] using hacc
    have hhalt :
        M.machine.halting
          (M.machine.run t (initialTMConfig M.machine x)).state = true := by
      cases hh : M.machine.halting
          (M.machine.run t (initialTMConfig M.machine x)).state <;>
        cases ha : M.accepting
          (M.machine.run t (initialTMConfig M.machine x)).state <;>
        simp_all
    have hrejected :
        M.accepting
          (M.machine.run t (initialTMConfig M.machine x)).state = false := by
      cases hh : M.machine.halting
          (M.machine.run t (initialTMConfig M.machine x)).state <;>
        cases ha : M.accepting
          (M.machine.run t (initialTMConfig M.machine x)).state <;>
        simp_all
    exact ⟨hhalt, hrejected⟩
  · rintro ⟨hhalt, hrejected⟩
    refine ⟨M.machine.run t (initialTMConfig M.machine x), ?_, ?_⟩
    · rw [complement_runBranches_to_tm_run M t
        (initialTMConfig M.machine x)]
      simp
    · change
        Bool.and
          (M.machine.halting
            (M.machine.run t (initialTMConfig M.machine x)).state)
          (!(M.accepting
            (M.machine.run t (initialTMConfig M.machine x)).state)) = true
      have hh :
          M.machine.halting
            (M.machine.run t (initialTMConfig M.machine x)).state = true := hhalt
      simp [hh, hrejected]

/-- Concrete SAT circuit whose satisfiability means that the deterministic
candidate has halted and rejected the supplied input within the given fuel. -/
def boundedRejectCircuit_DTM
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) : Circuit :=
  boundedExecCircuit_NTM (complementCandidate M) x t

theorem rejection_tableau_correctness
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    SATLanguage (boundedRejectCircuit_DTM M x t) ↔
      M.machine.HaltsWithin t (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run t (initialTMConfig M.machine x)).state = false := by
  simpa [boundedRejectCircuit_DTM] using
    (tableau_correctness_iff (complementCandidate M) x t).trans
      (complement_acceptsWithin_iff_rejects_at_fuel M x t)

theorem rejection_tableau_encoded_length_poly
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    (encodeCircuit (boundedRejectCircuit_DTM M x t)).length ≤
      tableauEncodingCoeff (complementCandidate M) *
        (x.length + t + 1)^4 := by
  simpa [boundedRejectCircuit_DTM] using
    boundedExec_encoded_length_poly (complementCandidate M) x t

#print axioms MCore.Real.P02DeterministicRejectionTableau.complement_runBranches_to_tm_run
#print axioms MCore.Real.P02DeterministicRejectionTableau.complement_acceptsWithin_iff_rejects_at_fuel
#print axioms MCore.Real.P02DeterministicRejectionTableau.rejection_tableau_correctness
#print axioms MCore.Real.P02DeterministicRejectionTableau.rejection_tableau_encoded_length_poly

end P02DeterministicRejectionTableau
end Real
end MCore
