import MCore.Real.P01WitnessIndexedReadPreserving

namespace MCore.Real.P01GapTolerantRead

-- 1. Tape real após consumo: witness ++ brancos ++ resto
def evalCursorStackEndTape (w : List Bool) (gap : Nat) (rem : List Bool) : List Bool :=
  w ++ List.replicate gap false ++ rem

-- 2. Leitor tolerante à lacuna
def gapTolerantRead : Nat → List Bool → Option Bool
  | _, [] => none
  | 0, b :: _ => some b
  | n+1, _ :: bs => gapTolerantRead n bs

@[simp]
theorem gapTolerantRead_zero (b : Bool) (bs : List Bool) :
  gapTolerantRead 0 (b :: bs) = some b := rfl

theorem gapTolerantRead_succ (n : Nat) (b : Bool) (bs : List Bool) :
  gapTolerantRead (n+1) (b :: bs) = gapTolerantRead n bs := rfl

theorem gapTolerantRead_length_lt (i : Nat) (l : List Bool) (h : i < l.length) :
  (gapTolerantRead i l).isSome = true := by
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp [gapTolerantRead]
    | succ n =>
      simp [gapTolerantRead]
      exact ih n (by simp at h ⊢; omega)

-- 3. CORE - proof-complete - fecha o layout evalCursorStackEndTape
theorem gapTolerant_append_left (i : Nat) (l₁ l₂ : List Bool) (h : i < l₁.length) :
  gapTolerantRead i (l₁ ++ l₂) = gapTolerantRead i l₁ := by
  induction l₁ generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp [gapTolerantRead]
    | succ n => simp [gapTolerantRead]; exact ih n (by simp at h ⊢; omega)

theorem gapTolerant_correct :
  ∀ (i : Nat) (witness : List Bool),
    i < witness.length →
    gapTolerantRead i witness = witness[i]? := by
  intro i witness hi
  induction witness generalizing i with
  | nil =>
      simp at hi
  | cons hd tl ih =>
      cases i with
      | zero =>
          rfl
      | succ n =>
          have hi' : n < tl.length := by
            simpa using hi
          simp only [gapTolerantRead]
          simpa using ih n hi'

theorem gapTolerant_correct_with_gap :
  ∀ (i : Nat) (witness rem : List Bool) (gap : Nat),
    i < witness.length →
    gapTolerantRead i (evalCursorStackEndTape witness gap rem) = witness[i]? := by
  intro i witness rem gap hi
  unfold evalCursorStackEndTape
  have h1 :
      gapTolerantRead i (witness ++ List.replicate gap false ++ rem) =
        gapTolerantRead i witness := by
    simpa [List.append_assoc] using
      gapTolerant_append_left i witness (List.replicate gap false ++ rem) hi
  rw [h1]
  exact gapTolerant_correct i witness hi

theorem gapTolerant_zero_eq_preserving :
  ∀ (i : Nat) (witness : List Bool),
    gapTolerantRead i witness = witness[i]? := by
  intro i witness
  induction witness generalizing i with
  | nil => simp [gapTolerantRead]
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp [gapTolerantRead]; exact ih n

-- 4. Caso 000 físico com lacuna - 6/6 completo
def physicalEvalStep_input_gapTolerant (i : Nat) (tape : List Bool) : Bool :=
  (gapTolerantRead i tape).getD false

theorem input000_with_gap_refines :
  ∀ i witness gap rem,
    i < witness.length →
    physicalEvalStep_input_gapTolerant i
        (evalCursorStackEndTape witness gap rem) =
      (witness[i]?).getD false := by
  intro i w gap rem hi
  unfold physicalEvalStep_input_gapTolerant
  rw [gapTolerant_correct_with_gap i w rem gap hi]

/-- Marker for this list-level helper only.  It is not a certificate for the
single-TM physical evaluator or for P01. -/
def listLevelInputHelperBuilt : Bool := true

theorem listLevelInputHelperBuilt_eq :
  listLevelInputHelperBuilt = true := rfl

end MCore.Real.P01GapTolerantRead
