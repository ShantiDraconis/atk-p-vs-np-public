import MCore.Real.P01CheckedEvalRunBoundedCertificate
import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01CheckedEvalRunExactOutcome

open CanonicalFinalProof
open CircuitK1
open CanonicalSATWitness
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunCircuitCertificate
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierInvariant
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/--
Exact cursor form of a whole-circuit checked outcome.

For nonterminal continuations the consumed-source counter is not existential:
it is exactly the input consumed counter plus the canonical encoding length of
the circuit that was evaluated.  Terminal root runs retain the ordinary final
configuration shape because no further child composition needs the cursor.
-/
def ExactCheckedLoopOutcome
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (startConsumed : Nat)
    (phi : Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig) : Prop :=
  match tail, frames with
  | [], [] =>
      ∃ tape : Tape (Option Bool),
        cfg = { state := .final value, tape := tape }
  | _, _ =>
      ∃ padding : Nat,
        cfg =
          { state := .have mode (.start value),
            tape :=
              evalCursorStackEndTape witness
                (startConsumed + (encodeCircuit phi).length)
                tail (encodeEvalFrames frames) padding }

/-- Exact cursor outcomes project to the pre-existing checked-loop outcome. -/
theorem exactOutcome_to_checkedOutcome
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (startConsumed : Nat)
    (phi : Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig)
    (h :
      ExactCheckedLoopOutcome witness mode value startConsumed
        phi tail frames cfg) :
    CheckedLoopOutcome witness mode value tail frames cfg := by
  cases tail with
  | nil =>
      cases frames with
      | nil =>
          exact h
      | cons f fs =>
          rcases h with ⟨padding, hcfg⟩
          exact ⟨startConsumed + (encodeCircuit phi).length, padding, hcfg⟩
  | cons b bs =>
      rcases h with ⟨padding, hcfg⟩
      exact ⟨startConsumed + (encodeCircuit phi).length, padding, hcfg⟩

/--
The exact consumed counter automatically preserves the global layout bound.
This is the conservation law needed by binary-node composition.
-/
theorem exactOutcome_layout
    (n startConsumed : Nat)
    (phi : Circuit)
    (tail : BitString)
    (frames : List EvalFrame)
    (hLayout :
      CheckedLayoutBound n startConsumed
        (encodeCircuit phi ++ tail)
        (encodeEvalFrames frames)) :
    CheckedLayoutBound n
      (startConsumed + (encodeCircuit phi).length)
      tail (encodeEvalFrames frames) :=
  after_exact_circuit n startConsumed phi tail
    (encodeEvalFrames frames) hLayout

/--
Stronger bounded certificate used for recursive composition.

It has the same machine, runtime budget, and semantic result as the existing
bounded certificate, but records exact source consumption in every nonterminal
outcome.  Therefore it is a strengthening, not an equivalent-hypothesis
wrapper: it has a kernel-checked projection to the existing certificate.
-/
def ExactBoundedCheckedCircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit) : Prop :=
  modeCheck mode phi = true →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
    CheckedLayoutBound n consumed
      (encodeCircuit phi ++ tail) (encodeEvalFrames frames) →
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m ≤ checkedCircuitBudget phi n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      ExactCheckedLoopOutcome witness (exitMode mode phi)
        (evalCircuit sigma phi) consumed phi tail frames cfg

/-- Forgetting the exact cursor equation recovers the existing bounded certificate. -/
theorem exactBounded_to_bounded
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit)
    (h :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness mode phi) :
    BoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  obtain ⟨m, hm, cfg, hrun, hout⟩ :=
    h hmode tail frames consumed padding n hLayout hlen hread
  exact ⟨m, hm, cfg, hrun,
    exactOutcome_to_checkedOutcome
      witness (exitMode mode phi) (evalCircuit sigma phi)
      consumed phi tail frames cfg hout⟩

/--
Exact composition-side layout after evaluating a left child while one
continuation frame remains on the stack.
-/
theorem exact_left_layout
    (n consumed : Nat)
    (left right : Circuit)
    (tail : BitString)
    (frame : EvalFrame)
    (frames : List EvalFrame)
    (h :
      CheckedLayoutBound n consumed
        (encodeCircuit left ++ encodeCircuit right ++ tail)
        (encodeEvalFrame frame ++ encodeEvalFrames frames)) :
    CheckedLayoutBound n
      (consumed + (encodeCircuit left).length)
      (encodeCircuit right ++ tail)
      (encodeEvalFrame frame ++ encodeEvalFrames frames) := by
  simpa [List.append_assoc] using
    after_exact_circuit n consumed left
      (encodeCircuit right ++ tail)
      (encodeEvalFrame frame ++ encodeEvalFrames frames) h

/--
Replacing the left binary continuation by the right-value continuation keeps
the exact layout budget unchanged.
-/
theorem exact_replace_binary_frame
    (n consumed : Nat)
    (source : BitString)
    (frames : List EvalFrame)
    (oldFrame newFrame : EvalFrame)
    (h :
      CheckedLayoutBound n consumed source
        (encodeEvalFrame oldFrame ++ encodeEvalFrames frames)) :
    CheckedLayoutBound n consumed source
      (encodeEvalFrame newFrame ++ encodeEvalFrames frames) :=
  replace_top_frame_exact n consumed source
    (encodeEvalFrames frames) oldFrame newFrame h

#print axioms MCore.Real.P01CheckedEvalRunExactOutcome.exactOutcome_to_checkedOutcome
#print axioms MCore.Real.P01CheckedEvalRunExactOutcome.exactOutcome_layout
#print axioms MCore.Real.P01CheckedEvalRunExactOutcome.exactBounded_to_bounded
#print axioms MCore.Real.P01CheckedEvalRunExactOutcome.exact_left_layout
#print axioms MCore.Real.P01CheckedEvalRunExactOutcome.exact_replace_binary_frame

end P01CheckedEvalRunExactOutcome
end Real
end MCore
