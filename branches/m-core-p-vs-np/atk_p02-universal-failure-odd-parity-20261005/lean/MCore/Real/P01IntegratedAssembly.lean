import MCore.Real.P01NTMSeqRun
import MCore.Real.P01GuessedWitnessRelation
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01IntegratedAssembly

/-!
# Integrated P01 assembly: two phases → `Nonempty P01MachineConstruction`

This module closes every integration obligation of P01 that is independent of
the two concrete machines:

* one finite-control NTM over `Fin (n + 1)` (state relabelling of `seq`);
* `blank_none`;
* a single polynomial bound `tPrep n + 1 + tVer n`;
* global `HaltsWithin` from `P01NTMSeqRun.seq_haltsWithin`;
* `AcceptsWithin ↔ SATBits circuitBitEncoding` from
  `P01NTMSeqRun.seq_acceptsWithin_iff` and
  `P01GuessedWitnessRelation.satBits_iff_guessed_witness`.

What remains is exactly two machine-level objects, stated as structures with no
endpoint proposition among their fields:

* `P01PrepPhase`: parser + witness guess, handing off `layout bs w` for every
  witness `w` of length `bs.length`, and nothing else;
* `P01VerifierPhase layout`: a physical verifier that, from `layout bs w`,
  halts and accepts iff `VerifyBits bs w`.

`VerifyBits` is the concrete bit relation (decode, CNF, evaluate under the
guessed bits); it is not `SATBits` and is not the endpoint.
-/

open CanonicalFinalProof CanonicalCircuitBits CanonicalSATBoundary
open P01NTMRunLaws P01NTMPhaseSeq P01NTMSeqRun P01GuessedWitnessRelation
open P01FinalCertificate

/-! ## State relabelling -/

variable {S T Sym : Type}

/-- Relabel the control states of an NTM along `enc` with left inverse `dec`. -/
def relabel (M : NTM S Sym) (enc : S → T) (dec : T → S) : NTM T Sym where
  initial := enc M.initial
  blank := M.blank
  transition := fun q y =>
    (M.transition (dec q) y).map (fun t => (enc t.1, t.2.1, t.2.2))
  accepting := fun q => M.accepting (dec q)
  rejecting := fun q => M.rejecting (dec q)

theorem relabel_simulation (M : NTM S Sym) (enc : S → T) (dec : T → S)
    (hdec : ∀ s, dec (enc s) = s) :
    Simulation M (relabel M enc dec) enc where
  accepting := fun s => by simp [relabel, hdec]
  rejecting := fun s => by simp [relabel, hdec]
  successors := fun c _ => by
    simp only [NTM.successors, relabel, hdec, List.map_map]
    apply List.map_congr_left
    intro t _
    rfl

theorem relabel_halted_iff (M : NTM S Sym) (enc : S → T) (dec : T → S)
    (hdec : ∀ s, dec (enc s) = s) (c : Configuration S Sym) :
    Halted (relabel M enc dec) (liftConfig enc c) ↔ Halted M c := by
  simp [Halted, relabel, liftConfig, hdec]

theorem relabel_haltsWithin_iff (M : NTM S Sym) (enc : S → T) (dec : T → S)
    (hdec : ∀ s, dec (enc s) = s) (n : Nat) (c : Configuration S Sym) :
    (relabel M enc dec).HaltsWithin n (liftConfig enc c) ↔ M.HaltsWithin n c := by
  have hsim := relabel_simulation M enc dec hdec
  rw [haltsWithin_iff_halted, haltsWithin_iff_halted]
  constructor
  · intro h z hz
    exact (relabel_halted_iff M enc dec hdec z).1
      (h _ ((mem_runBranches_map M _ enc hsim n c _).2 ⟨z, hz, rfl⟩))
  · intro h z hz
    rcases (mem_runBranches_map M _ enc hsim n c z).1 hz with ⟨d, hd, rfl⟩
    exact (relabel_halted_iff M enc dec hdec d).2 (h d hd)

theorem relabel_acceptsWithin_iff (M : NTM S Sym) (enc : S → T) (dec : T → S)
    (hdec : ∀ s, dec (enc s) = s) (n : Nat) (c : Configuration S Sym) :
    (relabel M enc dec).AcceptsWithin n (liftConfig enc c) ↔ M.AcceptsWithin n c := by
  have hsim := relabel_simulation M enc dec hdec
  constructor
  · rintro ⟨z, hz, hacc⟩
    rcases (mem_runBranches_map M _ enc hsim n c z).1 hz with ⟨d, hd, rfl⟩
    exact ⟨d, hd, by simpa [relabel, liftConfig, hdec] using hacc⟩
  · rintro ⟨d, hd, hacc⟩
    exact ⟨liftConfig enc d, (mem_runBranches_map M _ enc hsim n c _).2 ⟨d, hd, rfl⟩,
      by simpa [relabel, liftConfig, hdec] using hacc⟩

/-! ## `Fin` encoding of a sum of finite controls -/

def sumToFin (a b : Nat) : Sum (Fin (a + 1)) (Fin (b + 1)) → Fin (a + b + 1 + 1)
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr j => ⟨a + 1 + j.val, by omega⟩

def finToSum (a b : Nat) (k : Fin (a + b + 1 + 1)) : Sum (Fin (a + 1)) (Fin (b + 1)) :=
  if h : k.val < a + 1 then Sum.inl ⟨k.val, h⟩
  else Sum.inr ⟨k.val - (a + 1), by omega⟩

theorem finToSum_sumToFin (a b : Nat) (s : Sum (Fin (a + 1)) (Fin (b + 1))) :
    finToSum a b (sumToFin a b s) = s := by
  cases s with
  | inl i =>
      simp [finToSum, sumToFin, i.isLt]
  | inr j =>
      have h : ¬ (a + 1 + j.val < a + 1) := by omega
      simp only [finToSum, sumToFin, h, dite_false]
      congr
      omega

/-! ## Polynomial bounds are closed under `tA + 1 + tB` -/

theorem poly_seq (tA tB : TimeBound)
    (hA : PolynomialTimeBound tA) (hB : PolynomialTimeBound tB) :
    PolynomialTimeBound (fun n => tA n + 1 + tB n) := by
  rcases hA with ⟨c1, e1, h1⟩
  rcases hB with ⟨c2, e2, h2⟩
  refine ⟨c1 + 1 + c2, e1 + e2, ?_⟩
  intro n
  show tA n + 1 + tB n ≤ (c1 + 1 + c2) * (n + 1) ^ (e1 + e2)
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hX1 : (n + 1) ^ e1 ≤ (n + 1) ^ (e1 + e2) :=
    Nat.pow_le_pow_right hpos (by omega)
  have hX2 : (n + 1) ^ e2 ≤ (n + 1) ^ (e1 + e2) :=
    Nat.pow_le_pow_right hpos (by omega)
  have hone : 1 ≤ (n + 1) ^ (e1 + e2) := Nat.pow_pos hpos
  have hA' : tA n ≤ c1 * (n + 1) ^ (e1 + e2) :=
    Nat.le_trans (h1 n) (Nat.mul_le_mul_left c1 hX1)
  have hB' : tB n ≤ c2 * (n + 1) ^ (e1 + e2) :=
    Nat.le_trans (h2 n) (Nat.mul_le_mul_left c2 hX2)
  generalize (n + 1) ^ (e1 + e2) = X at *
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-! ## The two remaining machine objects -/

/-- Parser + witness-guess phase.  From the canonical input tape of `bs`, its
accepting branches hand off exactly the tapes `layout bs w`, one for every
witness `w` of length `bs.length`. -/
structure P01PrepPhase where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  disjoint : ∀ q, machine.accepting q = true → machine.rejecting q = false
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  layout : BitString → BitString → Tape (Option Bool)
  halts : ∀ bs : BitString,
    machine.HaltsWithin (timeBound bs.length) (initialNTMConfig machine bs)
  sound : ∀ (bs : BitString) (d : Configuration (Fin (stateCount + 1)) (Option Bool)),
    d ∈ machine.runBranches (timeBound bs.length) [initialNTMConfig machine bs] →
    machine.accepting d.state = true →
    ∃ w : BitString, w.length = bs.length ∧ d.tape = layout bs w
  complete : ∀ (bs w : BitString), w.length = bs.length →
    ∃ d ∈ machine.runBranches (timeBound bs.length) [initialNTMConfig machine bs],
      machine.accepting d.state = true ∧ d.tape = layout bs w

/-- Physical verifier phase: from the handed-off tape it halts within a
polynomial bound in the source length, and accepts iff the concrete bit
relation `VerifyBits bs w` holds. -/
structure P01VerifierPhase (layout : BitString → BitString → Tape (Option Bool)) where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts : ∀ bs w : BitString, w.length = bs.length →
    machine.HaltsWithin (timeBound bs.length) ⟨machine.initial, layout bs w⟩
  correct : ∀ bs w : BitString, w.length = bs.length →
    (machine.AcceptsWithin (timeBound bs.length) ⟨machine.initial, layout bs w⟩ ↔
      VerifyBits bs w)

/-! ## Assembly -/

section Assembly

variable (P : P01PrepPhase) (V : P01VerifierPhase P.layout)

abbrev seqMachine := seq P.machine V.machine

def integratedMachine :
    NTM (Fin (P.stateCount + V.stateCount + 1 + 1)) (Option Bool) :=
  relabel (seqMachine P V) (sumToFin P.stateCount V.stateCount)
    (finToSum P.stateCount V.stateCount)

def integratedTime : TimeBound :=
  fun n => P.timeBound n + 1 + V.timeBound n

theorem hblank : P.machine.blank = V.machine.blank := by
  rw [P.blank_none, V.blank_none]

theorem initial_config_eq (bs : BitString) :
    initialNTMConfig (integratedMachine P V) bs =
      liftConfig (sumToFin P.stateCount V.stateCount)
        (L P.machine V.machine (initialNTMConfig P.machine bs)) := rfl

theorem verifier_halts_on_handoffs (bs : BitString) :
    ∀ d ∈ P.machine.runBranches (P.timeBound bs.length)
        [initialNTMConfig P.machine bs],
      P.machine.accepting d.state = true →
      V.machine.HaltsWithin (V.timeBound bs.length) (handoff P.machine V.machine d) := by
  intro d hd hacc
  rcases P.sound bs d hd hacc with ⟨w, hw, htape⟩
  have := V.halts bs w hw
  simpa [handoff, htape] using this

theorem integrated_halts (bs : BitString) :
    (integratedMachine P V).HaltsWithin (integratedTime P V bs.length)
      (initialNTMConfig (integratedMachine P V) bs) := by
  rw [initial_config_eq, integratedMachine,
    relabel_haltsWithin_iff _ _ _ (finToSum_sumToFin _ _)]
  exact seq_haltsWithin P.machine V.machine (hblank P V) P.disjoint
    (V.timeBound bs.length) (P.timeBound bs.length) _ (P.halts bs)
    (verifier_halts_on_handoffs P V bs)

theorem integrated_accepts_iff (bs : BitString) :
    (integratedMachine P V).AcceptsWithin (integratedTime P V bs.length)
        (initialNTMConfig (integratedMachine P V) bs) ↔
      SATBits circuitBitEncoding bs := by
  rw [initial_config_eq, integratedMachine,
    relabel_acceptsWithin_iff _ _ _ (finToSum_sumToFin _ _),
    integratedTime,
    seq_acceptsWithin_iff P.machine V.machine (hblank P V) P.disjoint
      (P.timeBound bs.length) (V.timeBound bs.length) _ (P.halts bs)
      (verifier_halts_on_handoffs P V bs),
    satBits_iff_guessed_witness]
  constructor
  · rintro ⟨d, hd, hacc, hV⟩
    rcases P.sound bs d hd hacc with ⟨w, hw, htape⟩
    refine ⟨w, hw, (V.correct bs w hw).1 ?_⟩
    simpa [handoff, htape] using hV
  · rintro ⟨w, hw, hver⟩
    rcases P.complete bs w hw with ⟨d, hd, hacc, htape⟩
    refine ⟨d, hd, hacc, ?_⟩
    have := (V.correct bs w hw).2 hver
    simpa [handoff, htape] using this

/-- The integrated construction.  Every field is produced from the two phase
objects; no endpoint proposition is assumed. -/
def construction : P01MachineConstruction where
  stateCount := P.stateCount + V.stateCount + 1
  machine := integratedMachine P V
  blank_none := by
    show (seqMachine P V).blank = none
    exact P.blank_none
  timeBound := integratedTime P V
  time_poly := poly_seq _ _ P.time_poly V.time_poly
  halts := integrated_halts P V
  accepts_iff := integrated_accepts_iff P V

end Assembly

/-- The P01 construction gap reduces exactly to one prep phase and one
verifier phase over the same layout. -/
theorem p01_of_phases (P : P01PrepPhase) (V : P01VerifierPhase P.layout) :
    P01ConstructionGap :=
  ⟨construction P V⟩

theorem canonical_sat_machine_closure_of_phases
    (P : P01PrepPhase) (V : P01VerifierPhase P.layout) :
    CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 (p01_of_phases P V)

#print axioms P01IntegratedAssembly.construction
#print axioms P01IntegratedAssembly.p01_of_phases

end P01IntegratedAssembly
end Real
end MCore
