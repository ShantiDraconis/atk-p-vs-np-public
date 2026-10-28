import MCore.K10

namespace Audit.OfficialModel

abbrev BitStr := List Bool
abbrev OfficialLanguage := BitStr → Prop

inductive Direction where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

structure Tape where
  left : List Bool
  head : Bool
  right : List Bool
  deriving Repr

def Tape.write (t : Tape) (b : Bool) : Tape :=
  { t with head := b }

def Tape.moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] =>
      { left := [], head := false, right := t.head :: t.right }
  | b :: bs =>
      { left := bs, head := b, right := t.head :: t.right }

def Tape.moveRight (t : Tape) : Tape :=
  match t.right with
  | [] =>
      { left := t.head :: t.left, head := false, right := [] }
  | b :: bs =>
      { left := t.head :: t.left, head := b, right := bs }

def Tape.move (t : Tape) : Direction → Tape
  | .left => t.moveLeft
  | .stay => t
  | .right => t.moveRight

def inputTape : BitStr → Tape
  | [] => { left := [], head := false, right := [] }
  | b :: bs => { left := [], head := b, right := bs }

structure Action where
  nextState : Nat
  write : Bool
  move : Direction
  deriving Repr

structure Config where
  state : Nat
  tape : Tape
  deriving Repr

def applyAction (c : Config) (a : Action) : Config :=
  { state := a.nextState
    tape := (c.tape.write a.write).move a.move }

structure DTM where
  start : Nat
  accept : Nat
  reject : Nat
  delta : Nat → Bool → Action

namespace DTM

def halted (M : DTM) (c : Config) : Bool :=
  (c.state == M.accept) || (c.state == M.reject)

def initial (M : DTM) (x : BitStr) : Config :=
  { state := M.start, tape := inputTape x }

def next (M : DTM) (c : Config) : Config :=
  if M.halted c then
    c
  else
    applyAction c (M.delta c.state c.tape.head)

def run (M : DTM) : Nat → Config → Config
  | 0, c => c
  | n + 1, c => M.run n (M.next c)

end DTM

structure NTM where
  start : Nat
  accept : Nat
  reject : Nat
  delta : Nat → Bool → List Action

namespace NTM

def halted (M : NTM) (c : Config) : Bool :=
  (c.state == M.accept) || (c.state == M.reject)

def initial (M : NTM) (x : BitStr) : Config :=
  { state := M.start, tape := inputTape x }

def nextConfigs (M : NTM) (c : Config) : List Config :=
  if M.halted c then
    [c]
  else
    (M.delta c.state c.tape.head).map (fun a => applyAction c a)

def runSet (M : NTM) : Nat → List Config → List Config
  | 0, cs => cs
  | n + 1, cs => M.runSet n (cs.flatMap M.nextConfigs)

def acceptsWithin (M : NTM) (x : BitStr) (t : Nat) : Prop :=
  ∃ c, c ∈ M.runSet t [M.initial x] ∧ c.state = M.accept

def allHaltedWithin (M : NTM) (x : BitStr) (t : Nat) : Prop :=
  ∀ c, c ∈ M.runSet t [M.initial x] → M.halted c = true

end NTM

structure PolyBound where
  c : Nat
  k : Nat
  hk : 1 ≤ k

def polyEval (b : PolyBound) (n : Nat) : Nat :=
  b.c * (n + 1) ^ b.k

def DTM.DecidesWithin (M : DTM) (L : OfficialLanguage) (b : PolyBound) : Prop :=
  ∀ x,
    let c := M.run (polyEval b x.length) (M.initial x)
    M.halted c = true ∧ (c.state = M.accept ↔ L x)

def NTM.DecidesWithin (M : NTM) (L : OfficialLanguage) (b : PolyBound) : Prop :=
  ∀ x,
    M.allHaltedWithin x (polyEval b x.length) ∧
      (M.acceptsWithin x (polyEval b x.length) ↔ L x)

def OfficialP (L : OfficialLanguage) : Prop :=
  ∃ M : DTM, ∃ b : PolyBound, M.DecidesWithin L b

def OfficialNP (L : OfficialLanguage) : Prop :=
  ∃ M : NTM, ∃ b : PolyBound, M.DecidesWithin L b

def DTM.toNTM (M : DTM) : NTM :=
  { start := M.start
    accept := M.accept
    reject := M.reject
    delta := fun q s => [M.delta q s] }

theorem halted_toNTM (M : DTM) (c : Config) :
    M.toNTM.halted c = M.halted c := rfl

theorem nextConfigs_toNTM (M : DTM) (c : Config) :
    M.toNTM.nextConfigs c = [M.next c] := by
  unfold NTM.nextConfigs DTM.next
  rw [halted_toNTM]
  cases h : M.halted c <;>
    simp [h, DTM.toNTM]

theorem runSet_toNTM_singleton (M : DTM) (n : Nat) (c : Config) :
    M.toNTM.runSet n [c] = [M.run n c] := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp [NTM.runSet, DTM.run, nextConfigs_toNTM, ih]

theorem officialP_subset_officialNP :
    ∀ L : OfficialLanguage, OfficialP L → OfficialNP L := by
  intro L hP
  rcases hP with ⟨M, b, hM⟩
  refine ⟨M.toNTM, b, ?_⟩
  intro x
  have hdec := hM x
  let t := polyEval b x.length
  have hrun :
      M.toNTM.runSet t [M.toNTM.initial x] =
        [M.run t (M.initial x)] := by
    simpa [DTM.toNTM, NTM.initial, DTM.initial] using
      runSet_toNTM_singleton M t (M.initial x)
  constructor
  · intro c hc
    have hc' : c = M.run t (M.initial x) := by
      rw [hrun] at hc
      simpa using hc
    subst c
    simpa [t, NTM.halted, DTM.toNTM, DTM.halted] using hdec.1
  · constructor
    · intro hacc
      rcases hacc with ⟨c, hc, haccept⟩
      have hc' : c = M.run t (M.initial x) := by
        rw [hrun] at hc
        simpa using hc
      subst c
      exact (hdec.2.mp (by simpa [t] using haccept))
    · intro hL
      refine ⟨M.run t (M.initial x), ?_, ?_⟩
      · rw [hrun]
        simp
      · exact (hdec.2.mpr hL)

def canonicalInterface : MCore.ClassicalComplexityInterface OfficialLanguage :=
  { inP := OfficialP
    inNP := OfficialNP
    p_subset_np := officialP_subset_officialNP }

#print axioms Audit.OfficialModel.halted_toNTM
#print axioms Audit.OfficialModel.nextConfigs_toNTM
#print axioms Audit.OfficialModel.runSet_toNTM_singleton
#print axioms Audit.OfficialModel.officialP_subset_officialNP

end Audit.OfficialModel
