import MCore.Real.CanonicalSATParserTapeLayout

namespace MCore
namespace Real
namespace CanonicalSATSlotLog

/--
Work-region representation for outstanding parser slots.
true  = active slot
false = consumed slot tombstone

The region is separated from source input by the existing blank delimiter, so
false work cells cannot be confused with source bits.
-/
abbrev SlotLog := List Bool

def activeSlots : SlotLog → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + activeSlots bs

@[simp] theorem activeSlots_nil :
    activeSlots [] = 0 := rfl

@[simp] theorem activeSlots_true_cons (bs : SlotLog) :
    activeSlots (true :: bs) = activeSlots bs + 1 := by
  simp [activeSlots, Nat.add_comm]

@[simp] theorem activeSlots_false_cons (bs : SlotLog) :
    activeSlots (false :: bs) = activeSlots bs := by
  simp [activeSlots]

/-- Binary constructor update: net +1 outstanding slot. -/
def pushSlot (log : SlotLog) : SlotLog :=
  log ++ [true]

theorem activeSlots_append
    (a b : SlotLog) :
    activeSlots (a ++ b) = activeSlots a + activeSlots b := by
  induction a with
  | nil =>
      simp [activeSlots]
  | cons x xs ih =>
      cases x <;>
        simp [activeSlots, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem activeSlots_pushSlot (log : SlotLog) :
    activeSlots (pushSlot log) = activeSlots log + 1 := by
  simp [pushSlot, activeSlots_append, activeSlots]

/--
Consume the rightmost active slot. Tombstones are retained, so no tape
compaction is required.
-/
def popSlot : SlotLog → Option SlotLog
  | [] => none
  | b :: bs =>
      match popSlot bs with
      | some bs' => some (b :: bs')
      | none =>
          if b then some (false :: bs) else none

theorem popSlot_none_iff
    (log : SlotLog) :
    popSlot log = none ↔ activeSlots log = 0 := by
  induction log with
  | nil =>
      simp [popSlot, activeSlots]
  | cons b bs ih =>
      cases hpop : popSlot bs with
      | none =>
          have hzero : activeSlots bs = 0 := (ih.mp hpop)
          cases b <;>
            simp [popSlot, hpop, activeSlots, hzero]
      | some bs' =>
          have hne : activeSlots bs ≠ 0 := by
            intro hz
            have := ih.mpr hz
            rw [hpop] at this
            contradiction
          cases b <;>
            simp [popSlot, hpop, activeSlots, hne]

/-- Successful pop decreases the active-slot count by exactly one. -/
theorem activeSlots_popSlot
    (log log' : SlotLog)
    (h : popSlot log = some log') :
    activeSlots log = activeSlots log' + 1 := by
  induction log generalizing log' with
  | nil =>
      simp [popSlot] at h
  | cons b bs ih =>
      cases hpop : popSlot bs with
      | some bs' =>
          simp [popSlot, hpop] at h
          subst log'
          have hrec := ih bs' hpop
          cases b <;>
            simp [activeSlots, hrec, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]
      | none =>
          have hzero : activeSlots bs = 0 :=
            (popSlot_none_iff bs).mp hpop
          cases b with
          | false =>
              simp [popSlot, hpop] at h
          | true =>
              simp [popSlot, hpop] at h
              subst log'
              simp [activeSlots, hzero]

/-- A one-slot initial parser work region. -/
def initialSlotLog : SlotLog := [true]

@[simp] theorem initialSlotLog_active :
    activeSlots initialSlotLog = 1 := rfl

/--
Unary constructor update is identity: consume one slot and open one slot.
The physical work region therefore needs no modification.
-/
def keepSlot (log : SlotLog) : SlotLog := log

@[simp] theorem activeSlots_keepSlot (log : SlotLog) :
    activeSlots (keepSlot log) = activeSlots log := rfl

/-- A source-level slot count is represented by any log with that many active
true cells; physical tombstones are implementation detail. -/
def RepresentsSlots (slots : Nat) (log : SlotLog) : Prop :=
  activeSlots log = slots

theorem initialSlotLog_represents :
    RepresentsSlots 1 initialSlotLog := rfl

theorem pushSlot_represents
    {slots : Nat} {log : SlotLog}
    (h : RepresentsSlots slots log) :
    RepresentsSlots (slots + 1) (pushSlot log) := by
  unfold RepresentsSlots at h ⊢
  rw [activeSlots_pushSlot, h]

theorem popSlot_represents
    {slots : Nat} {log log' : SlotLog}
    (hslots : RepresentsSlots (slots + 1) log)
    (hpop : popSlot log = some log') :
    RepresentsSlots slots log' := by
  have hcount := activeSlots_popSlot log log' hpop
  rw [hslots] at hcount
  simp [RepresentsSlots] at *
  omega


/-- Zero active slots means every physical work cell is a false tombstone. -/
theorem activeSlots_zero_eq_replicate_false
    (log : SlotLog)
    (hzero : activeSlots log = 0) :
    log = List.replicate log.length false := by
  induction log with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          have hbs : activeSlots bs = 0 := by
            simpa [activeSlots] using hzero
          rw [ih hbs]
          simp [List.replicate_succ]
      | true =>
          simp [activeSlots] at hzero

/-- A successful pop has a unique rightmost-active shape: an arbitrary prefix,
one active true, then only false tombstones. The result changes exactly that
true to false. -/
theorem popSlot_decompose_rightmost
    (log log' : SlotLog)
    (hpop : popSlot log = some log') :
    ∃ pre k,
      log = pre ++ true :: List.replicate k false ∧
      log' = pre ++ false :: List.replicate k false := by
  induction log generalizing log' with
  | nil =>
      simp [popSlot] at hpop
  | cons b bs ih =>
      cases htail : popSlot bs with
      | some bs' =>
          have hsome : some (b :: bs') = some log' := by
            simpa [popSlot, htail] using hpop
          have hout : log' = b :: bs' := by
            exact (Option.some.inj hsome).symm
          rcases ih bs' htail with ⟨pre, k, hbs, hbs'⟩
          refine ⟨b :: pre, k, ?_, ?_⟩
          · simp [hbs, List.append_assoc]
          · subst log'
            simp [hbs', List.append_assoc]
      | none =>
          cases b with
          | false =>
              simp [popSlot, htail] at hpop
          | true =>
              have hsome : some (false :: bs) = some log' := by
                simpa [popSlot, htail] using hpop
              have hout : log' = false :: bs := by
                exact (Option.some.inj hsome).symm
              have hzero : activeSlots bs = 0 :=
                (popSlot_none_iff bs).mp htail
              have hrep := activeSlots_zero_eq_replicate_false bs hzero
              refine ⟨[], bs.length, ?_, ?_⟩
              · rw [hrep]
                simp only [List.length_replicate, List.nil_append]
              · subst log'
                rw [hrep]
                simp only [List.length_replicate, List.nil_append]

/-- Pop succeeds exactly when there is at least one active slot. -/
theorem popSlot_exists_iff_activeSlots_pos
    (log : SlotLog) :
    (∃ log', popSlot log = some log') ↔ 0 < activeSlots log := by
  constructor
  · rintro ⟨log', hpop⟩
    have hcount := activeSlots_popSlot log log' hpop
    omega
  · intro hpos
    cases h : popSlot log with
    | none =>
        have hzero := (popSlot_none_iff log).mp h
        omega
    | some log' =>
        exact ⟨log', rfl⟩

#print axioms MCore.Real.CanonicalSATSlotLog.activeSlots_append
#print axioms MCore.Real.CanonicalSATSlotLog.activeSlots_pushSlot
#print axioms MCore.Real.CanonicalSATSlotLog.popSlot_none_iff
#print axioms MCore.Real.CanonicalSATSlotLog.activeSlots_zero_eq_replicate_false
#print axioms MCore.Real.CanonicalSATSlotLog.popSlot_decompose_rightmost
#print axioms MCore.Real.CanonicalSATSlotLog.popSlot_exists_iff_activeSlots_pos
#print axioms MCore.Real.CanonicalSATSlotLog.activeSlots_popSlot
#print axioms MCore.Real.CanonicalSATSlotLog.pushSlot_represents
#print axioms MCore.Real.CanonicalSATSlotLog.popSlot_represents

end CanonicalSATSlotLog
end Real
end MCore
