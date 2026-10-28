import MCore.Real.CanonicalSATRecursiveParserPaths

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserWorkScans

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATRecursiveParserPaths

@[simp] theorem parser_not_halted_11 :
    parserMachine.halting (11 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_12 :
    parserMachine.halting (12 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_18 :
    parserMachine.halting (18 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_19 :
    parserMachine.halting (19 : Fin 25) = false := by decide

theorem step_source_11
    (left : List (Option Bool))
    (b : Bool)
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step (sourceConfig 11 left (b :: rest) suffix) =
      sourceConfig 11 (some b :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_source_18
    (left : List (Option Bool))
    (b : Bool)
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step (sourceConfig 18 left (b :: rest) suffix) =
      sourceConfig 18 (some b :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem run_source_11_to_delimiter
    (left : List (Option Bool))
    (bits : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run bits.length (sourceConfig 11 left bits suffix) =
      sourceConfig 11 ((bits.map some).reverse ++ left) [] suffix := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [sourceConfig_state, parser_not_halted_11]
      rw [step_source_11]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_source_18_to_delimiter
    (left : List (Option Bool))
    (bits : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run bits.length (sourceConfig 18 left bits suffix) =
      sourceConfig 18 ((bits.map some).reverse ++ left) [] suffix := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [sourceConfig_state, parser_not_halted_18]
      rw [step_source_18]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

def logConfig
    (q : Fin 25)
    (left : List (Option Bool))
    (log : List Bool) :
    Configuration (Fin 25) (Option Bool) :=
  match log with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem logConfig_state
    (q : Fin 25)
    (left : List (Option Bool))
    (log : List Bool) :
    (logConfig q left log).state = q := by
  cases log <;> rfl

theorem step_leaf_delimiter_to_log
    (left : List (Option Bool))
    (log : List Bool) :
    parserMachine.step
      (sourceConfig 11 left [] (log.map some)) =
      logConfig 12 (none :: left) log := by
  cases log <;>
    simp [parserMachine, sourceConfig, logConfig,
      TM.step, Tape.write, Tape.move]

theorem step_binary_delimiter_to_log
    (left : List (Option Bool))
    (log : List Bool) :
    parserMachine.step
      (sourceConfig 18 left [] (log.map some)) =
      logConfig 19 (none :: left) log := by
  cases log <;>
    simp [parserMachine, sourceConfig, logConfig,
      TM.step, Tape.write, Tape.move]

theorem step_log_12
    (left : List (Option Bool))
    (b : Bool)
    (rest : List Bool) :
    parserMachine.step (logConfig 12 left (b :: rest)) =
      logConfig 12 (some b :: left) rest := by
  cases rest <;>
    simp [parserMachine, logConfig, TM.step, Tape.write, Tape.move]

theorem step_log_19
    (left : List (Option Bool))
    (b : Bool)
    (rest : List Bool) :
    parserMachine.step (logConfig 19 left (b :: rest)) =
      logConfig 19 (some b :: left) rest := by
  cases rest <;>
    simp [parserMachine, logConfig, TM.step, Tape.write, Tape.move]

theorem run_log_12_to_end
    (left : List (Option Bool))
    (log : List Bool) :
    parserMachine.run log.length (logConfig 12 left log) =
      logConfig 12 ((log.map some).reverse ++ left) [] := by
  induction log generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [logConfig_state, parser_not_halted_12]
      rw [step_log_12]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_log_19_to_end
    (left : List (Option Bool))
    (log : List Bool) :
    parserMachine.run log.length (logConfig 19 left log) =
      logConfig 19 ((log.map some).reverse ++ left) [] := by
  induction log generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [logConfig_state, parser_not_halted_19]
      rw [step_log_19]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

#print axioms MCore.Real.CanonicalSATRecursiveParserWorkScans.run_source_11_to_delimiter
#print axioms MCore.Real.CanonicalSATRecursiveParserWorkScans.run_source_18_to_delimiter
#print axioms MCore.Real.CanonicalSATRecursiveParserWorkScans.run_log_12_to_end
#print axioms MCore.Real.CanonicalSATRecursiveParserWorkScans.run_log_19_to_end

end CanonicalSATRecursiveParserWorkScans
end Real
end MCore
