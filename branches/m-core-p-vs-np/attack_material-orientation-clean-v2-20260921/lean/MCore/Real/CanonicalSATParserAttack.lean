import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace CanonicalSATParserAttack

open CanonicalFinalProof

/-- Final states for the six constructor tags in CanonicalCircuitBits.encodeCircuit.
    State 12 is the malformed/truncated-tag sink. -/
def tagMachine : TM (Fin 13) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, symbol, .right)
        | some true  => (2, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 1 then
        match symbol with
        | some false => (3, symbol, .right)
        | some true  => (4, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 2 then
        match symbol with
        | some false => (5, symbol, .right)
        | _          => (12, symbol, .stay)
      else if q = 3 then
        match symbol with
        | some false => (6, symbol, .right)
        | some true  => (7, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 4 then
        match symbol with
        | some false => (8, symbol, .right)
        | some true  => (9, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 5 then
        match symbol with
        | some false => (10, symbol, .right)
        | some true  => (11, symbol, .right)
        | none       => (12, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => decide (6 ≤ q.val) }

@[simp] theorem tagMachine_initial_not_halted :
    tagMachine.halting (0 : Fin 13) = false := by
  decide

def tagInput (bitsPrefix : List Bool) (tail : BitString) : BitString :=
  bitsPrefix ++ tail

def tagConfig
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 13) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem tagConfig_state
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    (tagConfig q left bits).state = q := by
  cases bits <;> rfl

theorem initial_tagConfig
    (bits : BitString) :
    initialTMConfig tagMachine bits = tagConfig 0 [] bits := by
  cases bits <;> rfl

@[simp] theorem tagMachine_not_halted_at_one :
    tagMachine.halting (1 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_two :
    tagMachine.halting (2 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_three :
    tagMachine.halting (3 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_four :
    tagMachine.halting (4 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_five :
    tagMachine.halting (5 : Fin 13) = false := by decide
@[simp] theorem tagMachine_halted_at_twelve :
    tagMachine.halting (12 : Fin 13) = true := by decide

theorem tag_step_0_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 0 left (false :: rest)) =
      tagConfig 1 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_0_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 0 left (true :: rest)) =
      tagConfig 2 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_1_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 1 left (false :: rest)) =
      tagConfig 3 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_1_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 1 left (true :: rest)) =
      tagConfig 4 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_2_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 2 left (false :: rest)) =
      tagConfig 5 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_2_true_sink
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 2 left (true :: rest)) =
      tagConfig 12 left (true :: rest) := by
  simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_3_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 3 left (false :: rest)) =
      tagConfig 6 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_3_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 3 left (true :: rest)) =
      tagConfig 7 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_4_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 4 left (false :: rest)) =
      tagConfig 8 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_4_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 4 left (true :: rest)) =
      tagConfig 9 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_5_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 5 left (false :: rest)) =
      tagConfig 10 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_5_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 5 left (true :: rest)) =
      tagConfig 11 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_input_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, false] tail))).state = (6 : Fin 13) := by
  rw [show tagInput [false, false, false] tail = false :: false :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_three, tag_step_3_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_false_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, true] tail))).state = (7 : Fin 13) := by
  rw [show tagInput [false, false, true] tail = false :: false :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_three, tag_step_3_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_true_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, false] tail))).state = (8 : Fin 13) := by
  rw [show tagInput [false, true, false] tail = false :: true :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_four, tag_step_4_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_not_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, true] tail))).state = (9 : Fin 13) := by
  rw [show tagInput [false, true, true] tail = false :: true :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_four, tag_step_4_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_and_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, false] tail))).state = (10 : Fin 13) := by
  rw [show tagInput [true, false, false] tail = true :: false :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_five, tag_step_5_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_or_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, true] tail))).state = (11 : Fin 13) := by
  rw [show tagInput [true, false, true] tail = true :: false :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_five, tag_step_5_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_invalid_11_rejects
    (third : Bool)
    (tail : BitString) :
    (tagMachine.run 2
      (initialTMConfig tagMachine
        (tagInput [true, true, third] tail))).state = (12 : Fin 13) := by
  rw [show tagInput [true, true, third] tail = true :: true :: third :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_true_sink]
  simp [TM.run, tagConfig]

/-- The finite tag decoder is now concrete. The remaining parser obligation is
    unbounded recursive syntax bookkeeping on the same single tape. -/
structure RecursiveParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def RecursiveParserOperationalGap : Prop :=
  Nonempty RecursiveParserMachineCertificate

/-- Fail-proof: the legacy recursive-parser gate is under-specified.  A halted
    one-state machine inhabits it without recognizing a single constructor. -/
theorem legacy_recursive_parser_gate_is_trivially_inhabited :
    RecursiveParserOperationalGap := by
  let trivialMachine : TM (Fin 1) (Option Bool) :=
    { initial := 0
      blank := none
      transition := fun q symbol => (q, symbol, .stay)
      halting := fun _ => true }
  have hpoly : PolynomialTimeBound (fun _ => 0) := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp
  exact ⟨
    { stateCount := 0
      machine := trivialMachine
      timeBound := fun _ => 0
      time_poly := hpoly }⟩

/-- Hardened recursive parser boundary.  A witness must halt in polynomial
    time on every canonical bit tape and its accepting state must agree exactly
    with the total functional decoder.  This is the operational content that
    the legacy existence-only structure did not express. -/
structure CanonicalRecursiveParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ bits : BitString,
      machine.HaltsWithin
        (timeBound bits.length)
        (initialTMConfig machine bits)

  correct :
    ∀ bits : BitString,
      accepting
          (machine.run
            (timeBound bits.length)
            (initialTMConfig machine bits)).state = true
        ↔
      ∃ φ : CircuitK1.Circuit,
        CanonicalCircuitBits.decodeCircuit bits = some φ

def CanonicalRecursiveParserOperationalGap : Prop :=
  Nonempty CanonicalRecursiveParserMachineCertificate

/-- A genuine hardened parser also supplies the old existence-only payload.
    The converse is intentionally unavailable. -/
def CanonicalRecursiveParserMachineCertificate.toLegacy
    (C : CanonicalRecursiveParserMachineCertificate) :
    RecursiveParserMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem canonical_recursive_parser_closes_legacy_gap
    (h : CanonicalRecursiveParserOperationalGap) :
    RecursiveParserOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toLegacy⟩

#print axioms MCore.Real.CanonicalSATParserAttack.legacy_recursive_parser_gate_is_trivially_inhabited
#print axioms MCore.Real.CanonicalSATParserAttack.canonical_recursive_parser_closes_legacy_gap

#print axioms MCore.Real.CanonicalSATParserAttack.tag_input_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_false_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_true_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_not_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_and_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_or_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_invalid_11_rejects

end CanonicalSATParserAttack
end Real
end MCore
