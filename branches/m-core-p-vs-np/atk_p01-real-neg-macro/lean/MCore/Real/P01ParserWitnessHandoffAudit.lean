import MCore.Real.CanonicalSATParserLeafSourceProof
import MCore.Real.P01IntegratedExecutionMachine

namespace MCore
namespace Real
namespace P01ParserWitnessHandoffAudit

open CanonicalFinalProof
open CanonicalSATParserLeafSourceProof
open P01IntegratedExecutionMachine

/-- A successful nonempty-source parser terminal has blank under the head.
This is the exact reason it cannot be fed directly to a witness-preparation
machine that expects the original canonical source head. -/
theorem leafAcceptConfig_head_none
    (pad : Nat) (hpad : 0 < pad)
    (right : List (Option Bool)) :
    (leafAcceptConfig pad right).tape.head = none := by
  cases pad with
  | zero => omega
  | succ p =>
      simp [leafAcceptConfig, Tape.move, List.replicate_succ]

/-- Direct parser-accept -> canonical-input handoff is impossible for every
nonempty source: the parser terminal head is blank while canonical input has
the first Boolean under the head. -/
theorem leafAcceptConfig_ne_inputTape_cons
    (pad : Nat) (hpad : 0 < pad)
    (right : List (Option Bool))
    (b : Bool) (bs : BitString) :
    (leafAcceptConfig pad right).tape ≠ inputTape (b :: bs) := by
  intro h
  have hh := congrArg (fun t : Tape (Option Bool) => t.head) h
  have hh' :
      (leafAcceptConfig pad right).tape.head =
        (inputTape (b :: bs)).head := by
    simpa using hh
  rw [leafAcceptConfig_head_none pad hpad right] at hh'
  simp [inputTape] at hh'

/-- Fail-closed architecture verdict: any direct handoff claiming that the
accepting parser tape is already the original nonempty canonical source tape
is false.  A source-preservation/copy adapter is therefore mandatory. -/
def DirectParserToWitnessPrepValid : Prop :=
  ∀ (pad : Nat) (right : List (Option Bool))
    (b : Bool) (bs : BitString),
    0 < pad ->
    (leafAcceptConfig pad right).tape = inputTape (b :: bs)

theorem directParserToWitnessPrep_falsified :
    ¬ DirectParserToWitnessPrepValid := by
  intro h
  have heq := h 1 [] false [] (by decide)
  exact leafAcceptConfig_ne_inputTape_cons 1 (by decide) [] false [] heq

#print axioms MCore.Real.P01ParserWitnessHandoffAudit.leafAcceptConfig_ne_inputTape_cons
#print axioms MCore.Real.P01ParserWitnessHandoffAudit.directParserToWitnessPrep_falsified

end P01ParserWitnessHandoffAudit
end Real
end MCore
