/- ATK BATCH04: full source snapshot. Concatenation archival only, not kernel-certified. -/

/- SOURCE lean/MCore/Real/CanonicalSATWitness.lean BLOB 0585a266c7722e98b06296fadec948dfbed2763e -/
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace CanonicalSATWitness

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits

def varBound : Circuit → Nat
  | .input i => i + 1
  | .const _ => 0
  | .not c => varBound c
  | .and a b => max (varBound a) (varBound b)
  | .or a b => max (varBound a) (varBound b)

abbrev SATWitness (φ : Circuit) := Fin (varBound φ) → Bool

def assignmentOfWitness
    (φ : Circuit)
    (w : SATWitness φ) :
    Assignment :=
  fun i =>
    if h : i < varBound φ then
      w ⟨i, h⟩
    else
      false

theorem evalCircuit_eq_of_agree_below
    (φ : Circuit)
    (σ τ : Assignment)
    (hAgree : ∀ i, i < varBound φ → σ i = τ i) :
    evalCircuit σ φ = evalCircuit τ φ := by
  induction φ with
  | input i =>
      simp [varBound, evalCircuit, hAgree i (Nat.lt_succ_self i)]
  | const b =>
      rfl
  | not c ih =>
      have hSub : ∀ i, i < varBound c → σ i = τ i := by
        intro i hi
        exact hAgree i hi
      simp [varBound, evalCircuit, ih hSub]
  | and a b iha ihb =>
      have ha : ∀ i, i < varBound a → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hb : ∀ i, i < varBound b → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
      simp [varBound, evalCircuit, iha ha, ihb hb]
  | or a b iha ihb =>
      have ha : ∀ i, i < varBound a → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hb : ∀ i, i < varBound b → σ i = τ i := by
        intro i hi
        exact hAgree i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
      simp [varBound, evalCircuit, iha ha, ihb hb]

theorem witness_from_assignment_recovers_eval
    (φ : Circuit)
    (σ : Assignment) :
    evalCircuit
        (assignmentOfWitness φ (fun i => σ i.val))
        φ =
      evalCircuit σ φ := by
  apply evalCircuit_eq_of_agree_below
  intro i hi
  simp [assignmentOfWitness, hi]

def SATWitnessAccepts
    (φ : Circuit)
    (w : SATWitness φ) : Prop :=
  IsCNF φ ∧
    evalCircuit (assignmentOfWitness φ w) φ = true

theorem satLanguage_iff_exists_finite_witness
    (φ : Circuit) :
    SATLanguage φ ↔
      ∃ w : SATWitness φ, SATWitnessAccepts φ w := by
  constructor
  · rintro ⟨hCNF, σ, hEval⟩
    let w : SATWitness φ := fun i => σ i.val
    refine ⟨w, hCNF, ?_⟩
    have hRecover := witness_from_assignment_recovers_eval φ σ
    simpa [w, hEval] using hRecover
  · rintro ⟨w, hCNF, hEval⟩
    exact ⟨hCNF, assignmentOfWitness φ w, hEval⟩

theorem encodeNat_length
    (n : Nat) :
    (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, ih]

theorem varBound_le_encoded_length
    (φ : Circuit) :
    varBound φ ≤ (encodeCircuit φ).length := by
  induction φ with
  | input i =>
      simp [varBound, encodeCircuit, encodeNat_length]
  | const b =>
      cases b <;> simp [varBound, encodeCircuit]
  | not c ih =>
      simp [varBound, encodeCircuit]
      omega
  | and a b iha ihb =>
      simp [varBound, encodeCircuit]
      omega
  | or a b iha ihb =>
      simp [varBound, encodeCircuit]
      omega

def witnessBits
    {φ : Circuit}
    (w : SATWitness φ) :
    BitString :=
  List.ofFn w

theorem witnessBits_length
    {φ : Circuit}
    (w : SATWitness φ) :
    (witnessBits w).length = varBound φ := by
  simp [witnessBits]

theorem witness_bits_linear_bound
    {φ : Circuit}
    (w : SATWitness φ) :
    (witnessBits w).length ≤ (encodeCircuit φ).length := by
  rw [witnessBits_length]
  exact varBound_le_encoded_length φ

#print axioms MCore.Real.CanonicalSATWitness.evalCircuit_eq_of_agree_below
#print axioms MCore.Real.CanonicalSATWitness.witness_from_assignment_recovers_eval
#print axioms MCore.Real.CanonicalSATWitness.satLanguage_iff_exists_finite_witness
#print axioms MCore.Real.CanonicalSATWitness.varBound_le_encoded_length
#print axioms MCore.Real.CanonicalSATWitness.witness_bits_linear_bound

end CanonicalSATWitness
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATWitnessGuessNTM.lean BLOB 48ab49c6059d87231347e3335f5d9dbd87d013cf -/
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalSATWitnessGuessNTM

open CanonicalFinalProof

/-- Finite-control nondeterministic witness-bit generator.

Protocol: the current finite block determines the witness length.  At each
nonblank cell the machine nondeterministically writes false or true and moves
right.  At the first blank it enters state 1 and halts accepting.

The contents of the input block are irrelevant; only its finite length is used.
This lets a future integrated machine reserve an n-cell work block and generate
all Boolean witnesses of length n without storing n in control. -/
def witnessGuessMachine : NTM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | none => [(1, none, .stay)]
        | some _ =>
            [(0, some false, .right),
             (0, some true, .right)]
      else
        []
    accepting := fun q => q == 1
    rejecting := fun _ => false }

@[simp] theorem witnessGuessMachine_blank_none :
    witnessGuessMachine.blank = none := rfl

@[simp] theorem witnessGuessMachine_initial :
    witnessGuessMachine.initial = (0 : Fin 2) := rfl

def guessConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 2) (Option Bool) :=
  match bits with
  | [] =>
      { state := 0
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0
        tape := { left := left, head := some b, right := bs.map some } }

def doneConfig
    (left : List (Option Bool)) :
    Configuration (Fin 2) (Option Bool) :=
  { state := 1
    tape := { left := left, head := none, right := [] } }

@[simp] theorem guessConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (guessConfig left bits).state = (0 : Fin 2) := by
  cases bits <;> rfl

@[simp] theorem doneConfig_accepting
    (left : List (Option Bool)) :
    witnessGuessMachine.accepting (doneConfig left).state = true := by
  rfl

theorem witnessGuess_successors_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    witnessGuessMachine.successors (guessConfig left (b :: bs)) =
      [ guessConfig (some false :: left) bs,
        guessConfig (some true :: left) bs ] := by
  cases bs <;>
    simp [witnessGuessMachine, guessConfig, NTM.successors,
      NTM.stepBranch, Tape.write, Tape.move]

theorem witnessGuess_successors_nil
    (left : List (Option Bool)) :
    witnessGuessMachine.successors (guessConfig left []) =
      [doneConfig left] := by
  simp [witnessGuessMachine, guessConfig, doneConfig, NTM.successors,
    NTM.stepBranch, Tape.write, Tape.move]

def witnessGuessTimeBound : TimeBound :=
  fun n => n + 1

theorem witnessGuessTimeBound_poly :
    PolynomialTimeBound witnessGuessTimeBound := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [witnessGuessTimeBound]

/-- Type-level firewall: the guesser has fixed finite control and the canonical
fixed tape alphabet. -/
theorem witnessGuessMachine_canonical_type :
    Nonempty (NTM (Fin 2) (Option Bool)) :=
  ⟨witnessGuessMachine⟩

#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuess_successors_cons
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuess_successors_nil
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuessTimeBound_poly
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuessMachine_canonical_type

end CanonicalSATWitnessGuessNTM
end Real
end MCore


/- SOURCE lean/MCore/Real/FailProofAllGaps.lean BLOB e2c29e2b8311b64b34b4531ee3c425d9c1f0d091 -/
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace FailProofAllGaps

open CanonicalFinalProof

/-- A Skolemized fail proof: one explicit counterexample input for every
    deterministic polynomial-time candidate. -/
structure FailureGenerator (language : BitLanguage) where
  counterexample : PolyDTMCandidate → BitString
  fails :
    ∀ candidate : PolyDTMCandidate,
      ¬ candidate.CorrectAt language (counterexample candidate)

theorem failure_generator_implies_universal_failure
    {language : BitLanguage}
    (G : FailureGenerator language) :
    UniversalFailure language := by
  intro candidate
  exact ⟨G.counterexample candidate, G.fails candidate⟩

noncomputable def failureGeneratorOfUniversalFailure
    {language : BitLanguage}
    (h : UniversalFailure language) :
    FailureGenerator language := by
  classical
  let chooseInput : PolyDTMCandidate → BitString :=
    fun candidate => Classical.choose (h candidate)
  refine
    { counterexample := chooseInput
      fails := ?_ }
  intro candidate
  exact Classical.choose_spec (h candidate)

theorem failure_generator_iff_universal_failure
    {language : BitLanguage} :
    Nonempty (FailureGenerator language) ↔ UniversalFailure language := by
  constructor
  · rintro ⟨G⟩
    exact failure_generator_implies_universal_failure G
  · intro h
    exact ⟨failureGeneratorOfUniversalFailure h⟩

/-- External/official predicates on the same bit-language universe.
    This structure states only semantic equivalence of class membership. -/
structure ExternalModelMatch
    (officialP officialNP : BitLanguage → Prop) where
  p_match : ∀ language, InP language ↔ officialP language
  np_match : ∀ language, InNP language ↔ officialNP language

def OfficialPneqNP
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  ¬ ∀ language : BitLanguage, officialP language ↔ officialNP language

theorem internal_separation_transfers
    {officialP officialNP : BitLanguage → Prop}
    (hMatch : ExternalModelMatch officialP officialNP)
    (hInternal : PneqNP) :
    OfficialPneqNP officialP officialNP := by
  intro hEq
  apply hInternal
  intro language
  constructor
  · intro hP
    have hOfficialP := (hMatch.p_match language).mp hP
    have hOfficialNP := (hEq language).mp hOfficialP
    exact (hMatch.np_match language).mpr hOfficialNP
  · intro hNP
    have hOfficialNP := (hMatch.np_match language).mp hNP
    have hOfficialP := (hEq language).mpr hOfficialNP
    exact (hMatch.p_match language).mpr hOfficialP

/-- Exact three-gap payload:
    G1: one explicit NP target;
    G2: a universal fail generator for every deterministic poly-time candidate;
    G3: equivalence of the hardened internal model with the chosen external model. -/
structure FinalGapCertificate
    (officialP officialNP : BitLanguage → Prop) where
  target : BitLanguage
  target_in_np : InNP target
  fail_generator : FailureGenerator target
  model_match : ExternalModelMatch officialP officialNP

theorem final_gap_certificate_closes
    {officialP officialNP : BitLanguage → Prop}
    (cert : FinalGapCertificate officialP officialNP) :
    OfficialPneqNP officialP officialNP := by
  have hFail : UniversalFailure cert.target :=
    failure_generator_implies_universal_failure cert.fail_generator
  have hInternal : PneqNP :=
    target_failure_implies_p_ne_np cert.target_in_np hFail
  exact internal_separation_transfers cert.model_match hInternal

/-- If the external predicates are chosen to be the hardened internal model
    itself, only G1+G2 remain. -/
def InternalModelMatch :
    ExternalModelMatch InP InNP :=
  { p_match := fun _ => Iff.rfl
    np_match := fun _ => Iff.rfl }

#print axioms MCore.Real.FailProofAllGaps.failure_generator_implies_universal_failure
#print axioms MCore.Real.FailProofAllGaps.failureGeneratorOfUniversalFailure
#print axioms MCore.Real.FailProofAllGaps.failure_generator_iff_universal_failure
#print axioms MCore.Real.FailProofAllGaps.internal_separation_transfers
#print axioms MCore.Real.FailProofAllGaps.final_gap_certificate_closes

end FailProofAllGaps
end Real
end MCore


/- SOURCE lean/MCore/Real/FailProofFiniteAttack.lean BLOB 6875f6fefccc4d203734adfeba4932ee48a524f9 -/
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace FailProofFiniteAttack

open CanonicalFinalProof

def EmptyLanguage : BitLanguage := fun _ => False

def alwaysRejectMachine : TM (Fin 1) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol => (q, symbol, .stay)
    halting := fun _ => true }

def alwaysRejectCandidate : PolyDTMCandidate :=
  { stateCount := 0
    machine := alwaysRejectMachine
    blank_none := rfl
    accepting := fun _ => false
    timeBound := fun _ => 0
    time_poly := by
      refine ⟨0, 0, ?_⟩
      intro n
      simp [CanonicalFinalProof.PolynomialTimeBound] }

theorem alwaysRejectCandidate_correct :
    ∀ x : BitString,
      alwaysRejectCandidate.CorrectAt EmptyLanguage x := by
  intro x
  simp [PolyDTMCandidate.CorrectAt,
    alwaysRejectCandidate, alwaysRejectMachine,
    EmptyLanguage, initialTMConfig, TM.HaltsWithin, TM.run]

def emptyLanguageRealization : PolyDTMRealization EmptyLanguage :=
  { candidate := alwaysRejectCandidate
    decides := alwaysRejectCandidate_correct }

theorem empty_language_in_p : InP EmptyLanguage := by
  exact ⟨emptyLanguageRealization⟩

theorem empty_language_not_universal_failure :
    ¬ UniversalFailure EmptyLanguage := by
  intro h
  exact (universal_failure_implies_not_in_p h) empty_language_in_p

/-- Finite sampled failure evidence over an explicitly listed candidate set. -/
def FiniteFailureEvidence
    (language : BitLanguage)
    (candidates : List PolyDTMCandidate) : Prop :=
  ∀ candidate ∈ candidates,
    ∃ x : BitString, ¬ candidate.CorrectAt language x

theorem empty_sample_evidence :
    FiniteFailureEvidence EmptyLanguage [] := by
  intro candidate h
  cases h

/-- The invalid promotion rule under attack. -/
def FiniteToUniversalPrinciple : Prop :=
  ∀ language : BitLanguage,
    ∀ candidates : List PolyDTMCandidate,
      FiniteFailureEvidence language candidates →
      UniversalFailure language

/-- Formal countermodel: finite sampled evidence, even when syntactically valid,
    does not by itself imply a universal lower bound. -/
theorem finite_to_universal_principle_refuted :
    ¬ FiniteToUniversalPrinciple := by
  intro h
  have hUniversal : UniversalFailure EmptyLanguage :=
    h EmptyLanguage [] empty_sample_evidence
  exact empty_language_not_universal_failure hUniversal

#print axioms MCore.Real.FailProofFiniteAttack.alwaysRejectCandidate_correct
#print axioms MCore.Real.FailProofFiniteAttack.empty_language_in_p
#print axioms MCore.Real.FailProofFiniteAttack.empty_language_not_universal_failure
#print axioms MCore.Real.FailProofFiniteAttack.finite_to_universal_principle_refuted

end FailProofFiniteAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/FinalProof.lean BLOB 2413c8e879fde352ffd186f24a35db2d32f289e9 -/
import MCore.Real.SATMachine

namespace MCore
namespace Real

open CircuitK1

/-- Languages over the repository's concrete Circuit input type. -/
abbrev CircuitLanguage := Circuit → Prop

/-- Explicit polynomial bound for the concrete machine model.
    The coefficient and exponent are fixed for the machine, not for the input. -/
def PolynomialTimeBound (T : TimeBound) : Prop :=
  ∃ coefficient exponent : Nat, ∀ n : Nat,
    T n ≤ coefficient * (n + 1) ^ exponent

/-- A deterministic polynomial-time candidate, before claiming that it decides
    any particular language.  This is the domain quantified over by the direct
    fail-proof target. -/
structure PolyDTMCandidate where
  State : Type
  Symbol : Type
  machine : TM State Symbol
  accepting : State → Bool
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound

/-- Exact correctness condition for one input. -/
def PolyDTMCandidate.CorrectAt
    (candidate : PolyDTMCandidate)
    (language : CircuitLanguage)
    (φ : Circuit) : Prop :=
  candidate.machine.HaltsWithin
      (candidate.timeBound (CircuitK1.size φ))
      (candidate.encode φ) ∧
    (candidate.accepting
        (candidate.machine.run
          (candidate.timeBound (CircuitK1.size φ))
          (candidate.encode φ)).state = true
      ↔ language φ)

/-- A deterministic polynomial-time realization is exactly a candidate that is
    correct on every input. -/
structure PolyDTMRealization (language : CircuitLanguage) where
  candidate : PolyDTMCandidate
  decides :
    ∀ φ : Circuit, candidate.CorrectAt language φ

/-- Nondeterministic polynomial-time realization of one Circuit language.
    This reuses the already-certified NTM.DecidesWithin contract. -/
structure PolyNTMRealization (language : CircuitLanguage) where
  State : Type
  Symbol : Type
  machine : NTM State Symbol
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound
  decides :
    NTM.DecidesWithin
      machine encode CircuitK1.size language timeBound

/-- Concrete machine-model P and NP predicates used by the direct final-proof
    attack. These are internal definitions; equivalence with any external
    presentation of P/NP is a separate model-equivalence theorem. -/
def InP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyDTMRealization language)

def InNP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyNTMRealization language)

/-- Separation endpoint for the concrete machine model. -/
def MachinePneqNP : Prop :=
  ¬ ∀ language : CircuitLanguage, InP language ↔ InNP language

/-- SAT is in NP for this model. Constructing this witness is infrastructure,
    not the separation lower bound itself. -/
def SATInNP : Prop :=
  InNP SATLanguage

/-- Direct lower-bound target: no deterministic polynomial-time realization
    decides SAT in this concrete model. -/
def SATNotInP : Prop :=
  ¬ InP SATLanguage

/-- One explicit failure of one polynomial-time deterministic candidate. -/
def PolyDTMCandidate.FailsOn
    (candidate : PolyDTMCandidate)
    (language : CircuitLanguage)
    (φ : Circuit) : Prop :=
  ¬ candidate.CorrectAt language φ

/-- Operational universal lower bound: every deterministic polynomial-time SAT
    candidate has a concrete input on which it fails. -/
def UniversalSATFailure : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ φ : Circuit, candidate.FailsOn SATLanguage φ

/-- The fail-proof statement excludes every genuine SAT realization. -/
theorem universal_sat_failure_implies_sat_not_in_p
    (hFail : UniversalSATFailure) :
    SATNotInP := by
  intro hP
  rcases hP with ⟨realization⟩
  rcases hFail realization.candidate with ⟨φ, hBad⟩
  exact hBad (realization.decides φ)

/-- Conversely, non-membership in P forces a failing input for every candidate.
    This direction uses only classical propositional reasoning. -/
theorem sat_not_in_p_implies_universal_sat_failure
    (hNotP : SATNotInP) :
    UniversalSATFailure := by
  intro candidate
  apply Classical.byContradiction
  intro hNoFailure
  apply hNotP
  refine ⟨{ candidate := candidate, decides := ?_ }⟩
  intro φ
  apply Classical.byContradiction
  intro hBad
  exact hNoFailure ⟨φ, hBad⟩

theorem universal_sat_failure_iff_sat_not_in_p :
    UniversalSATFailure ↔ SATNotInP := by
  constructor
  · exact universal_sat_failure_implies_sat_not_in_p
  · exact sat_not_in_p_implies_universal_sat_failure

/-- Positive certificate form of the lower-bound target.
    Unlike timing evidence, its payload is universal over every polynomial-time
    deterministic candidate and produces a failing SAT instance for each one. -/
structure SATLowerBoundCertificate : Prop where
  fail_proof : UniversalSATFailure

theorem sat_not_in_p_of_lower_bound_certificate
    (cert : SATLowerBoundCertificate) :
    SATNotInP :=
  universal_sat_failure_implies_sat_not_in_p cert.fail_proof

theorem lower_bound_certificate_of_sat_not_in_p
    (hNotP : SATNotInP) :
    SATLowerBoundCertificate :=
  ⟨sat_not_in_p_implies_universal_sat_failure hNotP⟩

theorem sat_lower_bound_certificate_iff :
    SATLowerBoundCertificate ↔ SATNotInP := by
  constructor
  · exact sat_not_in_p_of_lower_bound_certificate
  · exact lower_bound_certificate_of_sat_not_in_p

/-- Direct endpoint compression. No NP-completeness theorem is required:
    one language in NP but outside P already separates the two classes. -/
theorem sat_boundary_implies_machine_p_ne_np
    (hNP : SATInNP)
    (hNotP : SATNotInP) :
    MachinePneqNP := by
  intro hEq
  exact hNotP ((hEq SATLanguage).mpr hNP)

/-- Certificate-shaped final theorem. -/
theorem sat_certificate_implies_machine_p_ne_np
    (hNP : SATInNP)
    (cert : SATLowerBoundCertificate) :
    MachinePneqNP :=
  sat_boundary_implies_machine_p_ne_np
    hNP (sat_not_in_p_of_lower_bound_certificate cert)

/-- The direct FINAL_PROOF residual.
    The first conjunct is the concrete NP witness.
    The second conjunct is the genuine universal deterministic fail proof.
    No benchmark, finite search, C12/C13 table, or elliptic-curve timing result
    inhabits this proposition by definition. -/
def FINAL_PROOF_RESIDUAL : Prop :=
  SATInNP ∧ SATLowerBoundCertificate

theorem final_proof_from_residual
    (h : FINAL_PROOF_RESIDUAL) :
    MachinePneqNP := by
  exact sat_certificate_implies_machine_p_ne_np h.1 h.2

#print axioms MCore.Real.universal_sat_failure_implies_sat_not_in_p
#print axioms MCore.Real.sat_not_in_p_implies_universal_sat_failure
#print axioms MCore.Real.universal_sat_failure_iff_sat_not_in_p
#print axioms MCore.Real.sat_boundary_implies_machine_p_ne_np
#print axioms MCore.Real.sat_certificate_implies_machine_p_ne_np
#print axioms MCore.Real.final_proof_from_residual

end Real
end MCore


/- SOURCE lean/MCore/Real/FinalProofAttack.lean BLOB ad3e12dd8a22a56ed638a264bd8cfa11d700c2a4 -/
import MCore.Real.FinalProof

namespace MCore
namespace Real
namespace FinalProofAttack

/-- Two-state halting shell encoded as Option Bool:
    none = running, some b = halted with answer bit b. -/
def smuggledMachine : TM (Option Bool) Bool :=
  { initial := none
    blank := false
    transition := fun state symbol =>
      match state with
      | none => (some symbol, symbol, .stay)
      | some b => (some b, symbol, .stay)
    halting := fun state =>
      match state with
      | none => false
      | some _ => true }

/-- Read acceptance directly from the halted answer state. -/
def smuggledAccepting : Option Bool → Bool
  | some true => true
  | _ => false

/-- This is precisely the loophole under attack:
    the arbitrary encoder computes membership before machine time starts and
    writes the answer bit into the initial tape. -/
noncomputable def smuggledEncode
    (language : CircuitLanguage)
    (φ : CircuitK1.Circuit) :
    Configuration (Option Bool) Bool :=
  letI : Decidable (language φ) := Classical.propDecidable (language φ)
  { state := none
    tape :=
      { left := []
        head := if language φ then true else false
        right := [] } }

noncomputable def smuggledCandidate
    (language : CircuitLanguage) :
    PolyDTMCandidate :=
  { State := Option Bool
    Symbol := Bool
    machine := smuggledMachine
    accepting := smuggledAccepting
    encode := smuggledEncode language
    timeBound := fun _ => 1
    encode_initial := by
      intro φ
      rfl
    time_poly := by
      refine ⟨1, 0, ?_⟩
      intro n
      simp [PolynomialTimeBound] }

theorem smuggledCandidate_correct
    (language : CircuitLanguage) :
    ∀ φ : CircuitK1.Circuit,
      (smuggledCandidate language).CorrectAt language φ := by
  intro φ
  classical
  by_cases h : language φ
  · simp [PolyDTMCandidate.CorrectAt,
      smuggledCandidate, smuggledMachine, smuggledAccepting,
      smuggledEncode, TM.HaltsWithin, TM.run, TM.step,
      Tape.write, Tape.move, h]
  · simp [PolyDTMCandidate.CorrectAt,
      smuggledCandidate, smuggledMachine, smuggledAccepting,
      smuggledEncode, TM.HaltsWithin, TM.run, TM.step,
      Tape.write, Tape.move, h]

noncomputable def smuggledRealization
    (language : CircuitLanguage) :
    PolyDTMRealization language :=
  { candidate := smuggledCandidate language
    decides := smuggledCandidate_correct language }

/-- FAIL TEST: under the current arbitrary-encode definition, every language
    has a one-step deterministic polynomial-time realization. -/
theorem every_language_inP_under_arbitrary_encode
    (language : CircuitLanguage) :
    InP language := by
  exact ⟨smuggledRealization language⟩

/-- Therefore SATNotInP is false in the current model independently of the
    actual P-vs-NP question. -/
theorem current_SATNotInP_refuted :
    ¬ SATNotInP := by
  intro h
  exact h (every_language_inP_under_arbitrary_encode SATLanguage)

/-- Consequently the current UniversalSATFailure target is also false. -/
theorem current_UniversalSATFailure_refuted :
    ¬ UniversalSATFailure := by
  intro h
  exact current_SATNotInP_refuted
    (universal_sat_failure_implies_sat_not_in_p h)

/-- And the certificate type is uninhabited in this flawed model. -/
theorem current_SATLowerBoundCertificate_refuted :
    ¬ SATLowerBoundCertificate := by
  intro cert
  exact current_SATNotInP_refuted
    (sat_not_in_p_of_lower_bound_certificate cert)

#print axioms MCore.Real.FinalProofAttack.smuggledCandidate_correct
#print axioms MCore.Real.FinalProofAttack.every_language_inP_under_arbitrary_encode
#print axioms MCore.Real.FinalProofAttack.current_SATNotInP_refuted
#print axioms MCore.Real.FinalProofAttack.current_UniversalSATFailure_refuted
#print axioms MCore.Real.FinalProofAttack.current_SATLowerBoundCertificate_refuted

end FinalProofAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/MachineRunLemmas.lean BLOB b6caca8af8fbe7962c38c8bf64d4871d69d9cca7 -/
import MCore.Real.Model

namespace MCore
namespace Real
namespace MachineRunLemmas

theorem run_halted
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config : Configuration State Symbol)
    (hhalt : machine.halting config.state = true)
    (fuel : Nat) :
    machine.run fuel config = config := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [TM.run, hhalt]

theorem run_add
    {State Symbol : Type}
    (machine : TM State Symbol)
    (m n : Nat)
    (config : Configuration State Symbol) :
    machine.run (m + n) config =
      machine.run n (machine.run m config) := by
  induction m generalizing config with
  | zero =>
      simp [TM.run]
  | succ m ih =>
      rw [Nat.succ_add]
      rw [TM.run]
      by_cases h : machine.halting config.state = true
      · simp only [h, if_pos]
        have hm :
            machine.run (m + 1) config = config :=
          run_halted machine config h (m + 1)
        rw [hm]
        exact (run_halted machine config h n).symm
      · have hf : machine.halting config.state = false := by
          cases hh : machine.halting config.state <;> simp_all
        simp only [hf, Bool.false_eq_true, if_false]
        rw [ih (machine.step config)]
        have hrunSucc :
            machine.run (m + 1) config =
              machine.run m (machine.step config) := by
          rw [TM.run]
          simp [hf]
        rw [hrunSucc]

theorem haltsWithin_mono
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config : Configuration State Symbol)
    {m n : Nat}
    (hmn : m ≤ n)
    (hhalt : machine.HaltsWithin m config) :
    machine.HaltsWithin n config := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold TM.HaltsWithin at hhalt ⊢
  rw [run_add]
  rw [run_halted machine (machine.run m config) hhalt]
  exact hhalt

theorem run_to_larger_fuel_of_halt
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config halted : Configuration State Symbol)
    {m n : Nat}
    (hmn : m ≤ n)
    (hrun : machine.run m config = halted)
    (hhalt : machine.halting halted.state = true) :
    machine.run n config = halted := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, hrun]
  exact run_halted machine halted hhalt k

#print axioms MCore.Real.MachineRunLemmas.run_add
#print axioms MCore.Real.MachineRunLemmas.run_halted
#print axioms MCore.Real.MachineRunLemmas.haltsWithin_mono
#print axioms MCore.Real.MachineRunLemmas.run_to_larger_fuel_of_halt

end MachineRunLemmas
end Real
end MCore


/- SOURCE lean/MCore/Real/Model.lean BLOB 75dc88485cb60edab758528d9c573b906bcd3c65 -/
import MCore.K5

namespace MCore.Real

inductive Direction where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

structure Tape (Symbol : Type) where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving Repr

namespace Tape

def write {Symbol : Type} (t : Tape Symbol) (symbol : Symbol) : Tape Symbol :=
  { t with head := symbol }

def move {Symbol : Type} (blank : Symbol) : Direction → Tape Symbol → Tape Symbol
  | .stay, t => t
  | .left, ⟨[], head, right⟩ =>
      ⟨[], blank, head :: right⟩
  | .left, ⟨next :: rest, head, right⟩ =>
      ⟨rest, next, head :: right⟩
  | .right, ⟨left, head, []⟩ =>
      ⟨head :: left, blank, []⟩
  | .right, ⟨left, head, next :: rest⟩ =>
      ⟨head :: left, next, rest⟩

end Tape

structure Configuration (State Symbol : Type) where
  state : State
  tape : Tape Symbol
  deriving Repr

/-- A deterministic single-tape machine with a total transition function. -/
structure TM (State Symbol : Type) where
  initial : State
  blank : Symbol
  transition : State → Symbol → State × Symbol × Direction
  halting : State → Bool

namespace TM

def step {State Symbol : Type} (machine : TM State Symbol)
    (config : Configuration State Symbol) : Configuration State Symbol :=
  let (nextState, nextSymbol, direction) :=
    machine.transition config.state config.tape.head
  { state := nextState
    tape := Tape.move machine.blank direction (config.tape.write nextSymbol) }

/-- The evaluator is total because fuel decreases structurally.  It does not
    assert that an arbitrary machine halts. -/
def run {State Symbol : Type} (machine : TM State Symbol) :
    Nat → Configuration State Symbol → Configuration State Symbol
  | 0, config => config
  | fuel + 1, config =>
      if machine.halting config.state then config
      else run machine fuel (machine.step config)

def HaltsWithin {State Symbol : Type} (machine : TM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  machine.halting (machine.run fuel config).state = true

def HaltsOn {State Symbol : Type} (machine : TM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.HaltsWithin fuel config

end TM

/-- A nondeterministic single-tape machine.  Each configuration has finitely
    many successors, represented by a list. -/
structure NTM (State Symbol : Type) where
  initial : State
  blank : Symbol
  transition : State → Symbol → List (State × Symbol × Direction)
  accepting : State → Bool
  rejecting : State → Bool

namespace NTM

def stepBranch {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol)
    (choice : State × Symbol × Direction) : Configuration State Symbol :=
  let (nextState, nextSymbol, direction) := choice
  { state := nextState
    tape := Tape.move machine.blank direction (config.tape.write nextSymbol) }

def successors {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : List (Configuration State Symbol) :=
  (machine.transition config.state config.tape.head).map
    (machine.stepBranch config)

/-- All branches reachable in at most the supplied fuel. -/
def runBranches {State Symbol : Type} (machine : NTM State Symbol) :
    Nat → List (Configuration State Symbol) → List (Configuration State Symbol)
  | 0, configs => configs
  | fuel + 1, configs =>
      let active := configs.filter fun c =>
        !(machine.accepting c.state || machine.rejecting c.state)
      let halted := configs.filter fun c =>
        machine.accepting c.state || machine.rejecting c.state
      runBranches machine fuel (halted ++ active.flatMap machine.successors)

def AcceptsWithin {State Symbol : Type} (machine : NTM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  ∃ reached ∈ machine.runBranches fuel [config],
    machine.accepting reached.state = true

def Accepts {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.AcceptsWithin fuel config

def HaltsWithin {State Symbol : Type} (machine : NTM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  ∀ reached ∈ machine.runBranches fuel [config],
    machine.accepting reached.state = true ∨
      machine.rejecting reached.state = true

def HaltsOn {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.HaltsWithin fuel config

end NTM

/-- A runtime bound indexed by encoded input size. -/
abbrev TimeBound := Nat → Nat

end MCore.Real


/- SOURCE lean/MCore/Real/P01DeterministicNTMEmbedding.lean BLOB de177f5cdceab7676746dfe19278a47a12bb887e -/
import MCore.Real.Model

namespace MCore
namespace Real
namespace P01DeterministicNTMEmbedding

/-- Embed a deterministic TM into the repository's NTM model by giving every
non-halting configuration exactly one successor.  A halted TM state is split
into accepting/rejecting according to the supplied terminal classifier. -/
def tmAsNTM
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) : NTM State Symbol where
  initial := M.initial
  blank := M.blank
  transition := fun q a =>
    if M.halting q then [] else [M.transition q a]
  accepting := fun q => M.halting q && accepting q
  rejecting := fun q => M.halting q && !accepting q

@[simp] theorem tmAsNTM_initial
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).initial = M.initial := rfl

@[simp] theorem tmAsNTM_blank
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).blank = M.blank := rfl

/-- On every non-halting state the embedded NTM has exactly the deterministic
TM step as its unique successor. -/
theorem tmAsNTM_successors_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).successors c = [M.step c] := by
  simp [tmAsNTM, NTM.successors, NTM.stepBranch, TM.step, h]

/-- A halted TM state is terminal in the embedded NTM. -/
theorem tmAsNTM_terminal_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h : M.halting q = true) :
    (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true := by
  cases ha : accepting q <;> simp [tmAsNTM, h, ha]

/-- Conversely, an NTM terminal state in the embedding is a halted TM state. -/
theorem tmAsNTM_terminal_implies_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h :
      (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) :
    M.halting q = true := by
  cases hm : M.halting q with
  | false =>
      rcases h with h | h <;> simp [tmAsNTM, hm] at h
  | true =>
      rfl


/-- One deterministic run step is reproduced by the singleton-branch NTM. -/
theorem runBranches_singleton_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).runBranches 1 [c] = [M.step c] := by
  have ha : (tmAsNTM M accepting).accepting c.state = false := by
    simp [tmAsNTM, h]
  have hr : (tmAsNTM M accepting).rejecting c.state = false := by
    simp [tmAsNTM, h]
  have hs := tmAsNTM_successors_of_not_halted M accepting c h
  simp [NTM.runBranches, ha, hr, hs]

/-- A halted TM configuration is already terminal for the embedded NTM. -/
theorem runBranches_singleton_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = true) :
    (tmAsNTM M accepting).runBranches 1 [c] = [c] := by
  have ht := tmAsNTM_terminal_of_halted M accepting c.state h
  rcases ht with ha | hr
  · simp [NTM.runBranches, ha]
  · simp [NTM.runBranches, hr]

/-- The embedded NTM classifies exactly the halted TM states as terminal. -/
theorem tmAsNTM_terminal_iff_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State) :
    ((tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) ↔
      M.halting q = true := by
  constructor
  · exact tmAsNTM_terminal_implies_halted M accepting q
  · exact tmAsNTM_terminal_of_halted M accepting q

#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_successors_of_not_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_of_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_implies_halted

end P01DeterministicNTMEmbedding
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EncodedEvaluator.lean BLOB 381f07e7b70003d8163d54edc5c5d1caaba7020e -/
import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATWitness
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01EncodedEvaluator

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1

/-- Streaming evaluator over the canonical bit encoding.
It consumes exactly one encoded circuit prefix and returns its Boolean value
together with the unconsumed tail.  No Circuit value is stored in control. -/
def evalEncodedCore :
    Nat → Assignment → BitString → Option (Bool × BitString)
  | 0, _, _ => none
  | fuel + 1, sigma, bits =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (sigma i, tail)
          | none => none
      | false :: false :: true :: rest =>
          some (false, rest)
      | false :: true :: false :: rest =>
          some (true, rest)
      | false :: true :: true :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (v, tail) => some (!v, tail)
          | none => none
      | true :: false :: false :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (l, rest') =>
              match evalEncodedCore fuel sigma rest' with
              | some (r, tail) => some (Bool.and l r, tail)
              | none => none
          | none => none
      | true :: false :: true :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (l, rest') =>
              match evalEncodedCore fuel sigma rest' with
              | some (r, tail) => some (Bool.or l r, tail)
              | none => none
          | none => none
      | _ => none

/-- On a canonical encoding, the streaming evaluator returns exactly the
semantic circuit value and preserves the external tail. -/
theorem evalEncodedCore_encode_append
    (sigma : Assignment)
    (c : Circuit)
    (tail : BitString)
    (fuel : Nat)
    (hFuel : CircuitK1.size c < fuel) :
    evalEncodedCore fuel sigma (encodeCircuit c ++ tail) =
      some (evalCircuit sigma c, tail) := by
  induction c generalizing fuel tail with
  | input i =>
      cases fuel with
      | zero => omega
      | succ f =>
          simp [evalEncodedCore, encodeCircuit, decodeNat_encodeNat_append,
            evalCircuit]
  | const b =>
      cases fuel with
      | zero => omega
      | succ f =>
          cases b <;> simp [evalEncodedCore, encodeCircuit, evalCircuit]
  | not c ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hc : CircuitK1.size c < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [evalEncodedCore, encodeCircuit, ih _ _ hc, evalCircuit]
  | and a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [evalEncodedCore, encodeCircuit, List.append_assoc,
            iha _ _ ha, ihb _ _ hb, evalCircuit]
  | or a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [evalEncodedCore, encodeCircuit, List.append_assoc,
            iha _ _ ha, ihb _ _ hb, evalCircuit]

/-- Fuel chosen only from the encoded input length is sufficient. -/
def evalEncoded
    (sigma : Assignment) (bits : BitString) : Option Bool :=
  match evalEncodedCore (bits.length + 1) sigma bits with
  | some (v, []) => some v
  | _ => none

theorem evalEncoded_encode
    (sigma : Assignment) (c : Circuit) :
    evalEncoded sigma (encodeCircuit c) =
      some (evalCircuit sigma c) := by
  have hFuel :
      CircuitK1.size c < (encodeCircuit c).length + 1 :=
    Nat.lt_succ_of_le (size_le_encodeCircuit_length c)
  have h :=
    evalEncodedCore_encode_append sigma c ([] : BitString)
      ((encodeCircuit c).length + 1) hFuel
  have h' :
      evalEncodedCore ((encodeCircuit c).length + 1) sigma (encodeCircuit c) =
        some (evalCircuit sigma c, []) := by
    simpa using h
  simp [evalEncoded, h']

/-- The streaming evaluator agrees with witness verification on the canonical
encoding.  This is the exact semantic specification the one-machine physical
verifier must refine. -/
theorem evalEncoded_witness
    (phi : Circuit)
    (w : CanonicalSATWitness.SATWitness phi) :
    evalEncoded (CanonicalSATWitness.assignmentOfWitness phi w)
        (encodeCircuit phi) =
      some (evalCircuit
        (CanonicalSATWitness.assignmentOfWitness phi w) phi) := by
  exact evalEncoded_encode
    (CanonicalSATWitness.assignmentOfWitness phi w) phi

#print axioms MCore.Real.P01EncodedEvaluator.evalEncodedCore_encode_append
#print axioms MCore.Real.P01EncodedEvaluator.evalEncoded_encode

end P01EncodedEvaluator
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EncodedFrameTape.lean BLOB 6119e11fd5589699e63ab15a872a761734e2c0aa -/
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01EncodedFrameTape

open CanonicalFinalProof
open P01EncodedStackEvaluator

/-- Fixed-width three-bit physical code for the seven semantic continuation
frames.  The code 111 is deliberately unused, giving a malformed-code reject
case to the future physical verifier. -/
def encodeEvalFrame : EvalFrame → BitString
  | .neg            => [false, false, false]
  | .andLeft        => [false, false, true]
  | .andRight false => [false, true, false]
  | .andRight true  => [false, true, true]
  | .orLeft         => [true, false, false]
  | .orRight false  => [true, false, true]
  | .orRight true   => [true, true, false]

def decodeEvalFrame : BitString → Option EvalFrame
  | [false, false, false] => some .neg
  | [false, false, true]  => some .andLeft
  | [false, true, false]  => some (.andRight false)
  | [false, true, true]   => some (.andRight true)
  | [true, false, false]  => some .orLeft
  | [true, false, true]   => some (.orRight false)
  | [true, true, false]   => some (.orRight true)
  | _ => none

@[simp] theorem decodeEvalFrame_encodeEvalFrame
    (f : EvalFrame) :
    decodeEvalFrame (encodeEvalFrame f) = some f := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

@[simp] theorem encodeEvalFrame_length
    (f : EvalFrame) :
    (encodeEvalFrame f).length = 3 := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

theorem encodeEvalFrame_injective :
    ∀ ⦃a b : EvalFrame⦄,
      encodeEvalFrame a = encodeEvalFrame b → a = b := by
  intro a b h
  have hd := congrArg decodeEvalFrame h
  simpa using hd

/-- Concatenated fixed-width representation of the continuation stack. -/
def encodeEvalFrames : List EvalFrame → BitString
  | [] => []
  | f :: fs => encodeEvalFrame f ++ encodeEvalFrames fs

@[simp] theorem encodeEvalFrames_nil :
    encodeEvalFrames [] = [] := rfl

@[simp] theorem encodeEvalFrames_cons
    (f : EvalFrame) (fs : List EvalFrame) :
    encodeEvalFrames (f :: fs) =
      encodeEvalFrame f ++ encodeEvalFrames fs := rfl

theorem encodeEvalFrames_length
    (fs : List EvalFrame) :
    (encodeEvalFrames fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [encodeEvalFrames, encodeEvalFrame_length, ih]
      omega

/-- Decode a full stack in three-bit blocks.  Any malformed/truncated code
fails rather than silently manufacturing a frame. -/
def decodeEvalFrames : BitString → Option (List EvalFrame)
  | [] => some []
  | a :: b :: c :: rest => do
      let f ← decodeEvalFrame [a,b,c]
      let fs ← decodeEvalFrames rest
      some (f :: fs)
  | _ => none

@[simp] theorem decodeEvalFrames_encodeEvalFrames
    (fs : List EvalFrame) :
    decodeEvalFrames (encodeEvalFrames fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | neg =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | andLeft =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | andRight b =>
          cases b <;>
            simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
              decodeEvalFrame, ih]
      | orLeft =>
          simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
            decodeEvalFrame, ih]
      | orRight b =>
          cases b <;>
            simp [encodeEvalFrames, encodeEvalFrame, decodeEvalFrames,
              decodeEvalFrame, ih]

/-- The frame stack consumes at most three tape cells per semantic frame. -/
theorem encodedFrames_linear_space
    (fs : List EvalFrame) (n : Nat)
    (h : fs.length ≤ n) :
    (encodeEvalFrames fs).length ≤ 3 * n := by
  rw [encodeEvalFrames_length]
  exact Nat.mul_le_mul_left 3 h

#print axioms MCore.Real.P01EncodedFrameTape.decodeEvalFrame_encodeEvalFrame
#print axioms MCore.Real.P01EncodedFrameTape.encodeEvalFrame_injective
#print axioms MCore.Real.P01EncodedFrameTape.decodeEvalFrames_encodeEvalFrames
#print axioms MCore.Real.P01EncodedFrameTape.encodedFrames_linear_space

end P01EncodedFrameTape
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EncodedStackEvaluator.lean BLOB 7bf30bbe3489cf801d314635ab10072721f63691 -/
import MCore.Real.P01EncodedEvaluator

namespace MCore
namespace Real
namespace P01EncodedStackEvaluator

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01EncodedEvaluator

/-- Finite continuation alphabet for direct prefix evaluation.
The only stored Boolean is the already-computed left operand of a binary node. -/
inductive EvalFrame where
  | neg
  | andLeft
  | andRight : Bool → EvalFrame
  | orLeft
  | orRight : Bool → EvalFrame
  deriving DecidableEq, Repr

/-- Explicit streaming evaluator state.  `value = none` means the next prefix
expression must be consumed; `some v` means a value is returning through the
continuation stack. -/
structure EvalState where
  bits : BitString
  frames : List EvalFrame
  value : Option Bool
  deriving Repr

def needExpr (bits : BitString) (frames : List EvalFrame := []) : EvalState :=
  { bits := bits, frames := frames, value := none }

def haveValue
    (v : Bool) (bits : BitString) (frames : List EvalFrame := []) : EvalState :=
  { bits := bits, frames := frames, value := some v }

/-- One semantic control transition of the iterative evaluator.  Tags and unary
indices are consumed from the bitstream; recursive structure is represented
only by the finite frame alphabet. -/
def evalStep (sigma : Assignment) : EvalState → Option EvalState
  | { bits := bits, frames := frames, value := none } =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (haveValue (sigma i) tail frames)
          | none => none
      | false :: false :: true :: rest =>
          some (haveValue false rest frames)
      | false :: true :: false :: rest =>
          some (haveValue true rest frames)
      | false :: true :: true :: rest =>
          some (needExpr rest (.neg :: frames))
      | true :: false :: false :: rest =>
          some (needExpr rest (.andLeft :: frames))
      | true :: false :: true :: rest =>
          some (needExpr rest (.orLeft :: frames))
      | _ => none
  | { bits := bits, frames := [], value := some _ } =>
      none
  | { bits := bits, frames := .neg :: frames, value := some v } =>
      some (haveValue (!v) bits frames)
  | { bits := bits, frames := .andLeft :: frames, value := some l } =>
      some (needExpr bits (.andRight l :: frames))
  | { bits := bits, frames := .andRight l :: frames, value := some r } =>
      some (haveValue (Bool.and l r) bits frames)
  | { bits := bits, frames := .orLeft :: frames, value := some l } =>
      some (needExpr bits (.orRight l :: frames))
  | { bits := bits, frames := .orRight l :: frames, value := some r } =>
      some (haveValue (Bool.or l r) bits frames)

/-- Iterate the finite-control semantics.  A halted/error state is stable under
additional fuel. -/
def evalRun : Nat → Assignment → EvalState → EvalState
  | 0, _, s => s
  | fuel + 1, sigma, s =>
      match evalStep sigma s with
      | none => s
      | some s' => evalRun fuel sigma s'

theorem evalRun_of_step_none
    (n : Nat) (sigma : Assignment) (s : EvalState)
    (h : evalStep sigma s = none) :
    evalRun n sigma s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evalRun, h]

theorem evalRun_add
    (m n : Nat) (sigma : Assignment) (s : EvalState) :
    evalRun (m + n) sigma s =
      evalRun n sigma (evalRun m sigma s) := by
  induction m generalizing s with
  | zero =>
      simp [evalRun]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [evalRun]
      cases h : evalStep sigma s with
      | none =>
          change s = evalRun n sigma s
          exact (evalRun_of_step_none n sigma s h).symm
      | some s' =>
          change evalRun (m + n) sigma s' =
            evalRun n sigma (evalRun m sigma s')
          exact ih s'

theorem evalRun_halted
    (n : Nat) (sigma : Assignment) (v : Bool) (bits : BitString) :
    evalRun n sigma (haveValue v bits []) =
      haveValue v bits [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evalRun, evalStep, haveValue, ih]

/-- Exact number of semantic control transitions required by one encoded
circuit, independent of the external tail and continuation. -/
def evalStepCount : Circuit → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => 1 + evalStepCount c + 1
  | .and a b => 1 + evalStepCount a + 1 + evalStepCount b + 1
  | .or a b => 1 + evalStepCount a + 1 + evalStepCount b + 1

/-- Main continuation theorem: after exactly `evalStepCount c` transitions,
the encoded circuit has been consumed, the external tail is untouched, the
original continuation stack is restored, and the exact semantic value is
available. -/
theorem evalRun_encode_append
    (sigma : Assignment)
    (c : Circuit)
    (tail : BitString)
    (frames : List EvalFrame) :
    evalRun (evalStepCount c) sigma
        (needExpr (encodeCircuit c ++ tail) frames) =
      haveValue (evalCircuit sigma c) tail frames := by
  induction c generalizing tail frames with
  | input i =>
      simp [evalStepCount, evalRun, evalStep, needExpr, haveValue,
        encodeCircuit, decodeNat_encodeNat_append, evalCircuit]
  | const b =>
      cases b <;>
        simp [evalStepCount, evalRun, evalStep, needExpr, haveValue,
          encodeCircuit, evalCircuit]
  | not c ih =>
      rw [show evalStepCount (.not c) =
          1 + (evalStepCount c + 1) by
            simp [evalStepCount, Nat.add_assoc]]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.not c) ++ tail) frames) =
            needExpr (encodeCircuit c ++ tail) (.neg :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [ih (tail := tail) (frames := .neg :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]
  | and a b iha ihb =>
      rw [show evalStepCount (.and a b) =
          1 + (evalStepCount a +
            (1 + (evalStepCount b + 1))) by
            simp [evalStepCount]; omega]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.and a b) ++ tail) frames) =
            needExpr
              (encodeCircuit a ++ (encodeCircuit b ++ tail))
              (.andLeft :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [iha
        (tail := encodeCircuit b ++ tail)
        (frames := .andLeft :: frames)]
      rw [evalRun_add]
      have hleft :
          evalRun 1 sigma
              (haveValue (evalCircuit sigma a)
                (encodeCircuit b ++ tail) (.andLeft :: frames)) =
            needExpr (encodeCircuit b ++ tail)
              (.andRight (evalCircuit sigma a) :: frames) := by
        rfl
      rw [hleft]
      rw [evalRun_add]
      rw [ihb
        (tail := tail)
        (frames := .andRight (evalCircuit sigma a) :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]
  | or a b iha ihb =>
      rw [show evalStepCount (.or a b) =
          1 + (evalStepCount a +
            (1 + (evalStepCount b + 1))) by
            simp [evalStepCount]; omega]
      rw [evalRun_add]
      have hfirst :
          evalRun 1 sigma
              (needExpr (encodeCircuit (.or a b) ++ tail) frames) =
            needExpr
              (encodeCircuit a ++ (encodeCircuit b ++ tail))
              (.orLeft :: frames) := by
        simp [evalRun, evalStep, needExpr, encodeCircuit, List.append_assoc]
      rw [hfirst]
      rw [evalRun_add]
      rw [iha
        (tail := encodeCircuit b ++ tail)
        (frames := .orLeft :: frames)]
      rw [evalRun_add]
      have hleft :
          evalRun 1 sigma
              (haveValue (evalCircuit sigma a)
                (encodeCircuit b ++ tail) (.orLeft :: frames)) =
            needExpr (encodeCircuit b ++ tail)
              (.orRight (evalCircuit sigma a) :: frames) := by
        rfl
      rw [hleft]
      rw [evalRun_add]
      rw [ihb
        (tail := tail)
        (frames := .orRight (evalCircuit sigma a) :: frames)]
      simp [evalRun, evalStep, haveValue, evalCircuit]

/-- The explicit control-step count is linear in circuit size. -/
theorem evalStepCount_le_three_mul_size
    (c : Circuit) :
    evalStepCount c ≤ 3 * CircuitK1.size c := by
  induction c with
  | input i =>
      simp [evalStepCount, CircuitK1.size]
  | const b =>
      simp [evalStepCount, CircuitK1.size]
  | not c ih =>
      simp [evalStepCount, CircuitK1.size] at *
      omega
  | and a b iha ihb =>
      simp [evalStepCount, CircuitK1.size] at *
      omega
  | or a b iha ihb =>
      simp [evalStepCount, CircuitK1.size] at *
      omega

theorem evalStepCount_le_three_mul_encoding
    (c : Circuit) :
    evalStepCount c ≤ 3 * (encodeCircuit c).length := by
  exact Nat.le_trans
    (evalStepCount_le_three_mul_size c)
    (Nat.mul_le_mul_left 3 (size_le_encodeCircuit_length c))

/-- Extra fuel after successful evaluation is inert, so a bound depending only
on encoded input length suffices. -/
theorem evalRun_encode_bounded
    (sigma : Assignment)
    (c : Circuit) :
    evalRun (3 * (encodeCircuit c).length) sigma
        (needExpr (encodeCircuit c) []) =
      haveValue (evalCircuit sigma c) [] [] := by
  have hle := evalStepCount_le_three_mul_encoding c
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, evalRun_add]
  rw [show encodeCircuit c = encodeCircuit c ++ [] by simp]
  rw [evalRun_encode_append]
  exact evalRun_halted k sigma (evalCircuit sigma c) []

#print axioms MCore.Real.P01EncodedStackEvaluator.evalRun_encode_append
#print axioms MCore.Real.P01EncodedStackEvaluator.evalStepCount_le_three_mul_encoding
#print axioms MCore.Real.P01EncodedStackEvaluator.evalRun_encode_bounded

end P01EncodedStackEvaluator
end Real
end MCore

