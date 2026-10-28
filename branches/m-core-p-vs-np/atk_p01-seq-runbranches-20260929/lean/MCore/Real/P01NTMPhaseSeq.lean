import MCore.Real.Model

namespace MCore
namespace Real
namespace P01NTMPhaseSeq

/-- Sequential composition of two NTMs over the same tape alphabet.

The first phase's accepting states are internal handoff states: in one stationary
step control moves to the second phase's initial state without changing the
tape.  A rejection in the first phase is a global rejection.  Only the second
phase contributes global acceptance. -/
def seq
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol)
    (B : NTM StateB Symbol) :
    NTM (Sum StateA StateB) Symbol where
  initial := Sum.inl A.initial
  blank := A.blank
  transition := fun q symbol =>
    match q with
    | Sum.inl qa =>
        if A.accepting qa then
          [(Sum.inr B.initial, symbol, .stay)]
        else if A.rejecting qa then
          []
        else
          (A.transition qa symbol).map
            (fun t => (Sum.inl t.1, t.2.1, t.2.2))
    | Sum.inr qb =>
        (B.transition qb symbol).map
          (fun t => (Sum.inr t.1, t.2.1, t.2.2))
  accepting := fun q =>
    match q with
    | Sum.inl _ => false
    | Sum.inr qb => B.accepting qb
  rejecting := fun q =>
    match q with
    | Sum.inl qa => A.rejecting qa
    | Sum.inr qb => B.rejecting qb

@[simp] theorem seq_initial
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol) :
    (seq A B).initial = Sum.inl A.initial := rfl

@[simp] theorem seq_blank
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol) :
    (seq A B).blank = A.blank := rfl

@[simp] theorem seq_accepting_left
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (qa : StateA) :
    (seq A B).accepting (Sum.inl qa) = false := rfl

@[simp] theorem seq_accepting_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (qb : StateB) :
    (seq A B).accepting (Sum.inr qb) = B.accepting qb := rfl

@[simp] theorem seq_rejecting_left
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (qa : StateA) :
    (seq A B).rejecting (Sum.inl qa) = A.rejecting qa := rfl

@[simp] theorem seq_rejecting_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (qb : StateB) :
    (seq A B).rejecting (Sum.inr qb) = B.rejecting qb := rfl

/-- An accepting state of phase A has exactly the stationary handoff successor
at phase B's initial state. -/
theorem seq_successors_handoff
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (c : Configuration StateA Symbol)
    (hacc : A.accepting c.state = true) :
    (seq A B).successors
      { state := Sum.inl c.state, tape := c.tape } =
      [{ state := Sum.inr B.initial, tape := c.tape }] := by
  simp [seq, NTM.successors, NTM.stepBranch, hacc, Tape.write, Tape.move]

/-- A nonterminal/nonrejecting A-state reproduces exactly A's successor list,
with only the control state injected into the left summand. -/
theorem seq_successors_left_active
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (c : Configuration StateA Symbol)
    (hacc : A.accepting c.state = false)
    (hrej : A.rejecting c.state = false) :
    (seq A B).successors
      { state := Sum.inl c.state, tape := c.tape } =
      (A.successors c).map
        (fun d => ({ state := Sum.inl d.state, tape := d.tape } :
          Configuration (Sum StateA StateB) Symbol)) := by
  simp [seq, NTM.successors, NTM.stepBranch, hacc, hrej]

/-- Inside phase B, the sequential machine reproduces B's successor list with
only the control state injected into the right summand. -/
theorem seq_successors_right
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (hblank : A.blank = B.blank)
    (c : Configuration StateB Symbol) :
    (seq A B).successors
      { state := Sum.inr c.state, tape := c.tape } =
      (B.successors c).map
        (fun d => ({ state := Sum.inr d.state, tape := d.tape } :
          Configuration (Sum StateA StateB) Symbol)) := by
  simp [seq, NTM.successors, NTM.stepBranch, hblank]

/-- The handoff itself preserves the complete physical tape exactly. -/
theorem handoff_preserves_tape
    {StateA StateB Symbol : Type}
    (A : NTM StateA Symbol) (B : NTM StateB Symbol)
    (c : Configuration StateA Symbol)
    (hacc : A.accepting c.state = true) :
    ∀ d ∈ (seq A B).successors
      { state := Sum.inl c.state, tape := c.tape },
      d.tape = c.tape := by
  rw [seq_successors_handoff A B c hacc]
  intro d hd
  simp only [List.mem_singleton] at hd
  subst d
  rfl

#print axioms MCore.Real.P01NTMPhaseSeq.seq_successors_handoff
#print axioms MCore.Real.P01NTMPhaseSeq.seq_successors_left_active
#print axioms MCore.Real.P01NTMPhaseSeq.seq_successors_right
#print axioms MCore.Real.P01NTMPhaseSeq.handoff_preserves_tape

end P01NTMPhaseSeq
end Real
end MCore
