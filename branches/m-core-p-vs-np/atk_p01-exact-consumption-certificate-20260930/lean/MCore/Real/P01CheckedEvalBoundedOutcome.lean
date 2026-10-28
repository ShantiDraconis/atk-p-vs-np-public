import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01CheckedEvalBoundedOutcome

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- A checked-loop result together with the physical layout invariant needed
to continue bounded evaluation.  The layout obligation is required only while
there is unread source or a continuation frame; a globally-final result has no
further recursive consumer. -/
def BoundedCheckedLoopOutcome
    (n : Nat)
    (witness : BitString)
    (mode : P01CNFMode.SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig) : Prop :=
  CheckedLoopOutcome witness mode value tail frames cfg ∧
    ((tail = [] ∧ frames = []) ∨
      ∃ consumed padding : Nat,
        cfg =
          { state := .have mode (.start value),
            tape :=
              evalCursorStackEndTape witness consumed tail
                (encodeEvalFrames frames) padding } ∧
        CheckedLayoutBound n consumed tail (encodeEvalFrames frames))

theorem to_checked
    {n : Nat} {witness : BitString} {mode : P01CNFMode.SyntaxMode}
    {value : Bool} {tail : BitString} {frames : List EvalFrame}
    {cfg : CheckedConfig}
    (h : BoundedCheckedLoopOutcome n witness mode value tail frames cfg) :
    CheckedLoopOutcome witness mode value tail frames cfg :=
  h.1

theorem layout_of_tail_ne_nil
    {n : Nat} {witness : BitString} {mode : P01CNFMode.SyntaxMode}
    {value : Bool} {tail : BitString} {frames : List EvalFrame}
    {cfg : CheckedConfig}
    (h : BoundedCheckedLoopOutcome n witness mode value tail frames cfg)
    (hne : tail ≠ []) :
    ∃ consumed padding : Nat,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed tail
              (encodeEvalFrames frames) padding } ∧
      CheckedLayoutBound n consumed tail (encodeEvalFrames frames) := by
  rcases h.2 with hfinal | hexact
  · exact False.elim (hne hfinal.1)
  · exact hexact

theorem layout_of_frames_ne_nil
    {n : Nat} {witness : BitString} {mode : P01CNFMode.SyntaxMode}
    {value : Bool} {tail : BitString} {frames : List EvalFrame}
    {cfg : CheckedConfig}
    (h : BoundedCheckedLoopOutcome n witness mode value tail frames cfg)
    (hne : frames ≠ []) :
    ∃ consumed padding : Nat,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed tail
              (encodeEvalFrames frames) padding } ∧
      CheckedLayoutBound n consumed tail (encodeEvalFrames frames) := by
  rcases h.2 with hfinal | hexact
  · exact False.elim (hne hfinal.2)
  · exact hexact

#print axioms MCore.Real.P01CheckedEvalBoundedOutcome.to_checked
#print axioms MCore.Real.P01CheckedEvalBoundedOutcome.layout_of_tail_ne_nil
#print axioms MCore.Real.P01CheckedEvalBoundedOutcome.layout_of_frames_ne_nil

end P01CheckedEvalBoundedOutcome
end Real
end MCore
