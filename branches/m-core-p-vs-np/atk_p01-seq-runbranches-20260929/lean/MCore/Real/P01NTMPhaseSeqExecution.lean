import MCore.Real.P01NTMPhaseSeq

namespace MCore
namespace Real
namespace P01NTMPhaseSeqExecution

open P01NTMPhaseSeq

def liftRight
    {StateA StateB Symbol : Type}
    (c : Configuration StateB Symbol) :
    Configuration (Sum StateA StateB) Symbol :=
  { state := Sum.inr c.state, tape := c.tape }

@[simp] theorem liftRight_state
    {StateA StateB Symbol : Type}
    (c : Configuration StateB Symbol) :
    (liftRight (StateA := StateA) c).state = Sum.inr c.state := rfl

@[simp] theorem liftRight_tape
    {StateA StateB Symbol : Type}
    (c : Configuration StateB Symbol) :
    (liftRight (StateA := StateA) c).tape = c.tape := rfl

theorem active_filter_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (cs : List (Configuration StateB Symbol)) :
    (cs.map (liftRight (StateA := StateA))).filter
        (fun c => !((seq A B).accepting c.state ||
          (seq A B).rejecting c.state)) =
      (cs.filter
        (fun c => !(B.accepting c.state || B.rejecting c.state))).map
          (liftRight (StateA := StateA)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [liftRight, ih]

theorem halted_filter_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (cs : List (Configuration StateB Symbol)) :
    (cs.map (liftRight (StateA := StateA))).filter
        (fun c => (seq A B).accepting c.state ||
          (seq A B).rejecting c.state) =
      (cs.filter
        (fun c => B.accepting c.state || B.rejecting c.state)).map
          (liftRight (StateA := StateA)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [liftRight, ih]

theorem successors_flatMap_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (hblank : A.blank = B.blank)
    (cs : List (Configuration StateB Symbol)) :
    (cs.map (liftRight (StateA := StateA))).flatMap
        (seq A B).successors =
      (cs.flatMap B.successors).map
        (liftRight (StateA := StateA)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [List.map_append, seq_successors_right A B hblank c, ih,
        liftRight]

/-- Once execution has entered phase B, the sequential machine reproduces
B's complete branch semantics exactly, for arbitrary fuel and arbitrary
configuration lists.  No endpoint assumption is used. -/
theorem runBranches_right_exact
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (hblank : A.blank = B.blank)
    (fuel : Nat)
    (cs : List (Configuration StateB Symbol)) :
    (seq A B).runBranches fuel
        (cs.map (liftRight (StateA := StateA))) =
      (B.runBranches fuel cs).map
        (liftRight (StateA := StateA)) := by
  induction fuel generalizing cs with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [NTM.runBranches]
      rw [active_filter_right A B cs]
      rw [halted_filter_right A B cs]
      rw [successors_flatMap_right A B hblank]
      rw [← List.map_append]
      exact ih
        ((cs.filter
          (fun c => B.accepting c.state || B.rejecting c.state)) ++
         cs.filter
          (fun c => !(B.accepting c.state || B.rejecting c.state)) |>.flatMap
            B.successors)

#print axioms MCore.Real.P01NTMPhaseSeqExecution.runBranches_right_exact

end P01NTMPhaseSeqExecution
end Real
end MCore
