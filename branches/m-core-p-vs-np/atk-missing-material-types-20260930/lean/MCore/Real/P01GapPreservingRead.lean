import MCore.Real.P01WitnessIndexedReadPreserving

/-!
# Gap-tolerant preserving witness read

The evaluator tape (`evalCursorStackEndTape`) keeps already-consumed source
cells as blanks, so between the witness and the unary index there is a gap of
`k` blanks in addition to the separator.  `preservingReadMachine` rejects on
that gap at its entry states.

`gapReadMachine` is the same finite control with exactly two entry transitions
changed:

* `advanceSep` on a blank keeps moving left (skips the gap) and, on the first
  witness bit, performs the capture/write directly;
* `finalSepNoMoved` on a blank keeps moving left and, on the first witness bit,
  reads it and starts the halting return.

Every other transition is identical.  The moved-prefix phase never re-enters
`indexNoMoved`, `advanceSep` or `finalSepNoMoved`, so from any moved-phase
configuration the two machines run identically (`gap_run_eq_preserving`).
The moved-phase lemmas are therefore proved once, for `preservingReadMachine`,
with the blank block generalized by an extra gap `g`, and transported.
-/

namespace MCore
namespace Real
namespace P01GapPreservingRead

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01WitnessIndexedRead
open MachineRunLemmas
open P01WitnessIndexedReadPreserving

/-! ## 1. The machine -/

def gapReadMachine : TM PreservingReadState (Option Bool) where
  initial := .indexNoMoved
  blank := none
  transition := fun q symbol =>
    match q with
    | .advanceSep =>
        match symbol with
        | none => (.advanceSep, none, .left)
        | some b => (.writeMoved b, none, .right)
    | .finalSepNoMoved =>
        match symbol with
        | none => (.finalSepNoMoved, none, .left)
        | some b => (.restoreHalt b, some b, .right)
    | q => preservingReadMachine.transition q symbol
  halting := preservingReadMachine.halting

/-! ## 2. Transfer from the moved phase -/

/-- States reachable after the entry phase. -/
def movedPhase : PreservingReadState → Bool
  | .indexNoMoved => false
  | .advanceSep => false
  | .finalSepNoMoved => false
  | _ => true

theorem transition_agree (q : PreservingReadState) (hq : movedPhase q = true)
    (s : Option Bool) :
    gapReadMachine.transition q s = preservingReadMachine.transition q s := by
  cases q <;> simp_all [movedPhase, gapReadMachine]

theorem transition_stays (q : PreservingReadState) (hq : movedPhase q = true)
    (s : Option Bool) :
    movedPhase (preservingReadMachine.transition q s).1 = true := by
  cases q <;> cases s <;> (try (rename_i v; cases v)) <;>
    simp [movedPhase, preservingReadMachine] at hq ⊢

theorem step_agree (c : Configuration PreservingReadState (Option Bool))
    (hc : movedPhase c.state = true) :
    gapReadMachine.step c = preservingReadMachine.step c := by
  unfold TM.step
  rw [transition_agree c.state hc]
  rfl

theorem step_stays (c : Configuration PreservingReadState (Option Bool))
    (hc : movedPhase c.state = true) :
    movedPhase (preservingReadMachine.step c).state = true := by
  unfold TM.step
  exact transition_stays c.state hc c.tape.head

/-- From any moved-phase configuration the gap machine and the original
preserving machine produce exactly the same run. -/
theorem gap_run_eq_preserving (n : Nat)
    (c : Configuration PreservingReadState (Option Bool))
    (hc : movedPhase c.state = true) :
    gapReadMachine.run n c = preservingReadMachine.run n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [TM.run]
      have hh : gapReadMachine.halting c.state =
          preservingReadMachine.halting c.state := rfl
      rw [hh]
      split
      · rfl
      · rw [step_agree c hc]
        exact ih _ (step_stays c hc)

/-! ## 3. Moved-prefix layout with an extra gap `g` and an arbitrary suffix -/

/-- Moved layout: `moved.length + g` blanks, the moved prefix, the separator
and the untouched witness suffix on the left; the unread source bits and then
an arbitrary suffix (e.g. separator + frame stack) on the right. -/
def gapMovedTape
    (moved rest : BitString) (x : Bool) (xs : BitString) (g : Nat)
    (suffix : List (Option Bool)) : Tape (Option Bool) :=
  { left := List.replicate (moved.length + g) none ++ moved.map some ++
      (none :: rest.map some),
    head := some x,
    right := xs.map some ++ suffix }

def gapMovedConfig
    (moved rest : BitString) (x : Bool) (xs : BitString) (g : Nat)
    (suffix : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved, tape := gapMovedTape moved rest x xs g suffix }

/-- One successor cycle with gap `g`. -/
theorem gapMoved_cycle
    (first b next : Bool)
    (movedTail witnessTail sourceTail : BitString) (g : Nat)
    (suffix : List (Option Bool)) :
    preservingReadMachine.run (4 * movedTail.length + 2 * g + 10)
      (gapMovedConfig (first :: movedTail) (b :: witnessTail)
        true (next :: sourceTail) g suffix) =
      gapMovedConfig ((first :: movedTail) ++ [b]) witnessTail
        next sourceTail g suffix := by
  let m : Nat := movedTail.length
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: (sourceTail.map some ++ suffix)
  let after : List (Option Bool) :=
    List.replicate (m + g) none ++ (none :: src)
  let stream : List (Option Bool) :=
    moved.reverse.map some ++ (none :: after)
  let restoredLeft : List (Option Bool) :=
    none :: (moved.map some ++ (some b :: none :: witnessSuffix))

  let C0 := gapMovedConfig moved (b :: witnessTail) true (next :: sourceTail) g suffix
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekMoved,
      tape :=
        { left :=
            List.replicate (m + g) none ++
              (some first ::
                (movedTail.map some ++
                  (none :: some b :: witnessSuffix))),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekMoved,
      tape :=
        { left :=
            movedTail.map some ++ (none :: some b :: witnessSuffix),
          head := some first,
          right := List.replicate (m + g + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .scanMoved,
      tape :=
        scanMovedTape movedTail b witnessSuffix
          (some first ::
            (List.replicate (m + g + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .capture,
      tape :=
        { left := witnessSuffix,
          head := some b,
          right := none :: stream } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnMoved,
      tape :=
        returnMovedTape moved.reverse
          (some b :: none :: witnessSuffix) after }
  let C6 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape restoredLeft after }
  let C6e : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape :=
        { left := restoredLeft,
          head := none,
          right := List.replicate (m + g) none ++ src } }
  let C7e : Configuration PreservingReadState (Option Bool) :=
    { state := .indexMoved,
      tape :=
        { left := List.replicate (m + g + 1) none ++ restoredLeft,
          head := some next,
          right := sourceTail.map some ++ suffix } }
  let C7 := gapMovedConfig (moved ++ [b]) witnessTail next sourceTail g suffix

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, witnessSuffix, src, gapMovedConfig, gapMovedTape]
    rw [show movedTail.length + 1 + g = (movedTail.length + g) + 1 by omega]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (m + g + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      seekMoved_over_blanks (m + g) first
        (movedTail.map some ++ (none :: some b :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      seekMoved_step_bit first b movedTail witnessSuffix
        (List.replicate (m + g + 1) none ++ (none :: src))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, stream, moved, after, src, m]
    simpa [List.reverse_cons, List.map_append,
      List.replicate_succ, List.append_assoc] using
      scanMoved_over_bits movedTail b witnessSuffix
        (some first ::
          (List.replicate (movedTail.length + g + 1) none ++
            (none :: (some next :: (sourceTail.map some ++ suffix)))))

  have h45 : preservingReadMachine.run 2 C4 = C5 := by
    dsimp [C4, C5, stream]
    simpa [returnMovedTape_eq_stream] using
      capture_write_to_stream b witnessSuffix
        (moved.reverse.map some ++ (none :: after))

  have h56 : preservingReadMachine.run (m + 2) C5 = C6 := by
    dsimp [C5, C6, restoredLeft, moved]
    simpa [moved, m] using
      returnMoved_over_bits moved.reverse
        (some b :: none :: witnessSuffix) after

  have h6eq : C6 = C6e := by
    dsimp [C6, C6e, after]
    exact congrArg
      (fun t : Tape (Option Bool) =>
        ({ state := .returnBlanks, tape := t } :
          Configuration PreservingReadState (Option Bool)))
      (rightStreamTape_blank_block (m + g) restoredLeft src)

  have h67 : preservingReadMachine.run (m + g + 2) C6e = C7e := by
    dsimp [C6e, C7e, src]
    simpa using
      returnBlanks_over_blanks (m + g) next restoredLeft
        (sourceTail.map some ++ suffix)

  have hleft :
      List.replicate (m + g + 1) none ++ restoredLeft =
        List.replicate ((moved ++ [b]).length + g) none ++
          (moved ++ [b]).map some ++ (none :: witnessSuffix) := by
    have h :=
      replicate_none_extend (m + g)
        (moved.map some ++ (some b :: none :: witnessSuffix))
    rw [show (moved ++ [b]).length + g = (m + g) + 2 by
      simp [moved, m]; omega]
    dsimp [restoredLeft] at h ⊢
    simpa [List.map_append, List.append_assoc] using h

  have h7eq : C7e = C7 := by
    dsimp [C7e, C7, gapMovedConfig, gapMovedTape]
    rw [hleft]

  have h02 : preservingReadMachine.run (1 + (m + g + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 : preservingReadMachine.run ((1 + (m + g + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (m + g + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run ((((1 + (m + g + 1)) + 1) + (m + 1)) + 2) C0 =
        C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (m + g + 1)) + 1) + (m + 1)) + 2) + (m + 2)) C0 = C6e := by
    rw [run_add, h05, h56, h6eq]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (m + g + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (m + g + 2))
        C0 = C7 := by
    rw [run_add, h06, h67, h7eq]

  have hFuel :
      4 * movedTail.length + 2 * g + 10 =
        ((((((1 + (m + g + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (m + g + 2)) := by
    dsimp [m]
    omega
  rw [hFuel]
  exact h07

/-! ## 4. Terminal read with gap `g` -/

/-- Terminal `false` with a nonempty moved prefix and gap `g`: halts with the
selected bit, restores the witness exactly and preserves source + suffix. -/
theorem gapMoved_false_finalize
    (first selected : Bool)
    (movedTail rest sourceTail : BitString) (g : Nat)
    (suffix : List (Option Bool)) :
    preservingReadMachine.run (5 * movedTail.length + g + 11)
      (gapMovedConfig (first :: movedTail) (selected :: rest)
        false sourceTail g suffix) =
      { state := .halt selected,
        tape :=
          { left := ((first :: movedTail) ++ (selected :: rest)).map some,
            head := none,
            right :=
              List.replicate (movedTail.length + g + 2) none ++
                (sourceTail.map some ++ suffix) } } := by
  let m : Nat := movedTail.length
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := rest.map some
  let src : List (Option Bool) := sourceTail.map some ++ suffix
  let after : List (Option Bool) :=
    List.replicate (m + g + 1) none ++ (none :: src)

  let C0 := gapMovedConfig moved (selected :: rest) false sourceTail g suffix
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            List.replicate (m + g) none ++
              (some first ::
                (movedTail.map some ++
                  (none :: some selected :: witnessSuffix))),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            movedTail.map some ++ (none :: some selected :: witnessSuffix),
          head := some first,
          right := after } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalScanMoved,
      tape := scanMovedTape movedTail selected witnessSuffix (some first :: after) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalReadMoved,
      tape :=
        { left := witnessSuffix,
          head := some selected,
          right := none :: (moved.reverse.map some ++ after) } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    restoreMovedConfig selected (some selected :: witnessSuffix)
      moved.reverse after
  let restoredWitness : List (Option Bool) :=
    moved.map some ++ (some selected :: witnessSuffix)
  let C6 : Configuration PreservingReadState (Option Bool) :=
    restoreMovedConfig selected restoredWitness [] after
  let C7 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt selected,
      tape :=
        { left := restoredWitness,
          head := none,
          right := List.replicate (m + g + 2) none ++ src } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, witnessSuffix, src, gapMovedConfig, gapMovedTape]
    rw [show movedTail.length + 1 + g = (movedTail.length + g) + 1 by omega]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (m + g + 1) C1 = C2 := by
    dsimp [C1, C2, after]
    simpa using
      finalSeekMoved_over_blanks (m + g) first
        (movedTail.map some ++ (none :: some selected :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      finalSeekMoved_step_bit first selected movedTail witnessSuffix after

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, moved]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      finalScanMoved_over_bits movedTail selected witnessSuffix
        (some first :: after)

  have h45 : preservingReadMachine.run 1 C4 = C5 := by
    dsimp [C4, C5, moved, after, src, witnessSuffix, restoreMovedConfig]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.reverse_cons, List.map_append,
      List.append_assoc]

  have h56 : preservingReadMachine.run (3 * moved.length) C5 = C6 := by
    dsimp [C5, C6, restoredWitness]
    simpa [moved] using
      restoreMoved_over_bits selected moved.reverse
        (some selected :: witnessSuffix) after

  have h67 : preservingReadMachine.run 3 C6 = C7 := by
    dsimp [C6, C7, restoreMovedConfig, restoredWitness, after, src, moved, m]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ,
      List.map_append, List.append_assoc]
    simpa using
      replicate_none_cons (movedTail.length + g) (sourceTail.map some ++ suffix)

  have h02 : preservingReadMachine.run (1 + (m + g + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 : preservingReadMachine.run ((1 + (m + g + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (m + g + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run ((((1 + (m + g + 1)) + 1) + (m + 1)) + 1) C0 =
        C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (m + g + 1)) + 1) + (m + 1)) + 1) + 3 * moved.length) C0 =
        C6 := by
    rw [run_add, h05, h56]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (m + g + 1)) + 1) + (m + 1)) + 1) + 3 * moved.length) + 3)
        C0 = C7 := by
    rw [run_add, h06, h67]

  have hFuel :
      5 * movedTail.length + g + 11 =
        ((((((1 + (m + g + 1)) + 1) + (m + 1)) + 1) + 3 * moved.length) + 3) := by
    simp [moved, m]
    omega
  rw [hFuel]
  simpa [C0, C7, moved, restoredWitness, src, m,
    List.map_append, List.append_assoc] using h07

/-! ## 5. Unary-index form and the moved-phase induction -/

/-- Moved configuration whose unread source starts with `encodeNat n ++ tail`. -/
def gapIdxConfig (moved rest : BitString) :
    Nat → BitString → Nat → List (Option Bool) →
      Configuration PreservingReadState (Option Bool)
  | 0, tail, g, suffix => gapMovedConfig moved rest false tail g suffix
  | n + 1, tail, g, suffix =>
      gapMovedConfig moved rest true (encodeNat n ++ tail) g suffix

theorem gapIdx_cycle
    (first b : Bool) (movedTail witnessTail tail : BitString)
    (n g : Nat) (suffix : List (Option Bool)) :
    preservingReadMachine.run (4 * movedTail.length + 2 * g + 10)
      (gapIdxConfig (first :: movedTail) (b :: witnessTail) (n + 1) tail g suffix) =
      gapIdxConfig ((first :: movedTail) ++ [b]) witnessTail n tail g suffix := by
  cases n with
  | zero =>
      simpa [gapIdxConfig, encodeNat] using
        gapMoved_cycle first b false movedTail witnessTail tail g suffix
  | succ n =>
      simpa [gapIdxConfig, encodeNat] using
        gapMoved_cycle first b true movedTail witnessTail
          (encodeNat n ++ tail) g suffix

/-- Exact moved-phase fuel with gap `g`. -/
def gapMovedFuel (movedLen g : Nat) : Nat → Nat
  | 0 => 5 * movedLen + g + 6
  | n + 1 => (4 * movedLen + 2 * g + 6) + gapMovedFuel (movedLen + 1) g n

theorem gapMoved_forall
    (first : Bool) (movedTail rest tail : BitString) (g : Nat)
    (suffix : List (Option Bool)) (n : Nat) (h : n < rest.length) :
    preservingReadMachine.run
      (gapMovedFuel (first :: movedTail).length g n)
      (gapIdxConfig (first :: movedTail) rest n tail g suffix) =
      { state := .halt (rest.getD n false),
        tape :=
          { left := ((first :: movedTail) ++ rest).map some,
            head := none,
            right :=
              List.replicate ((first :: movedTail).length + g + n + 1) none ++
                (tail.map some ++ suffix) } } := by
  induction n generalizing movedTail rest with
  | zero =>
      cases rest with
      | nil => simp at h
      | cons selected restTail =>
          have hf : gapMovedFuel (first :: movedTail).length g 0 =
              5 * movedTail.length + g + 11 := by
            simp [gapMovedFuel]; omega
          rw [hf]
          have hr : (first :: movedTail).length + g + 0 + 1 =
              movedTail.length + g + 2 := by simp; omega
          rw [hr]
          simpa [gapIdxConfig] using
            gapMoved_false_finalize first selected movedTail restTail tail g suffix
  | succ n ih =>
      cases rest with
      | nil => simp at h
      | cons selected restTail =>
          have htail : n < restTail.length := by simpa using h
          rw [show gapMovedFuel (first :: movedTail).length g (n + 1) =
              (4 * movedTail.length + 2 * g + 10) +
                gapMovedFuel (first :: (movedTail ++ [selected])).length g n by
              simp [gapMovedFuel]; omega]
          rw [run_add, gapIdx_cycle]
          change preservingReadMachine.run
              (gapMovedFuel (first :: (movedTail ++ [selected])).length g n)
              (gapIdxConfig (first :: (movedTail ++ [selected])) restTail n tail g
                suffix) = _
          rw [ih (movedTail := movedTail ++ [selected]) (rest := restTail) htail]
          simp [List.getD_cons_succ, List.map_append, List.append_assoc]
          omega

/-! ## 6. Entry phase of `gapReadMachine` (crosses the gap) -/

/-- Canonical gapped input: `k` gap blanks and the separator between the
witness and the unary index; `suffix` is whatever follows the source bits. -/
def gapReadTape (witness : BitString) (k : Nat) (x : Bool) (xs : BitString)
    (suffix : List (Option Bool)) : Tape (Option Bool) :=
  { left := List.replicate k none ++ (none :: witness.map some),
    head := some x,
    right := xs.map some ++ suffix }

def gapReadConfig (witness : BitString) (k : Nat) :
    Nat → BitString → List (Option Bool) →
      Configuration PreservingReadState (Option Bool)
  | 0, tail, suffix =>
      { state := .indexNoMoved, tape := gapReadTape witness k false tail suffix }
  | n + 1, tail, suffix =>
      { state := .indexNoMoved,
        tape := gapReadTape witness k true (encodeNat n ++ tail) suffix }

theorem advanceSep_over_blanks
    (k : Nat) (b : Bool) (left right : List (Option Bool)) :
    gapReadMachine.run (k + 1)
      { state := .advanceSep,
        tape := { left := List.replicate k none ++ (some b :: left),
                  head := none, right := right } } =
      { state := .advanceSep,
        tape := { left := left, head := some b,
                  right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega, TM.run]
      simp only [show gapReadMachine.halting (.advanceSep) = false by rfl,
        Bool.false_eq_true, if_false]
      change gapReadMachine.run (k + 1)
        { state := .advanceSep,
          tape := { left := List.replicate k none ++ (some b :: left),
                    head := none, right := none :: right } } = _
      rw [ih (none :: right)]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        congrArg (fun r : List (Option Bool) =>
          ({ state := .advanceSep,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
          (replicate_none_extend k right)

theorem finalSep_over_blanks
    (k : Nat) (b : Bool) (left right : List (Option Bool)) :
    gapReadMachine.run (k + 1)
      { state := .finalSepNoMoved,
        tape := { left := List.replicate k none ++ (some b :: left),
                  head := none, right := right } } =
      { state := .finalSepNoMoved,
        tape := { left := left, head := some b,
                  right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega, TM.run]
      simp only [show gapReadMachine.halting (.finalSepNoMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change gapReadMachine.run (k + 1)
        { state := .finalSepNoMoved,
          tape := { left := List.replicate k none ++ (some b :: left),
                    head := none, right := none :: right } } = _
      rw [ih (none :: right)]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        congrArg (fun r : List (Option Bool) =>
          ({ state := .finalSepNoMoved,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
          (replicate_none_extend k right)

/-- `returnBlanks` from a rightward stream of `k` blanks followed by a bit. -/
theorem returnBlanks_stream
    (k : Nat) (x : Bool) (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .returnBlanks,
        tape := rightStreamTape left (List.replicate k none ++ (some x :: right)) } =
      { state := .indexMoved,
        tape := { left := List.replicate k none ++ left, head := some x,
                  right := right } } := by
  induction k generalizing left with
  | zero =>
      simp [rightStreamTape, preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.returnBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      have hs : preservingReadMachine.step
          { state := .returnBlanks,
            tape := rightStreamTape left
              (List.replicate (k + 1) none ++ (some x :: right)) } =
          { state := .returnBlanks,
            tape := rightStreamTape (none :: left)
              (List.replicate k none ++ (some x :: right)) } := by
        cases k <;>
          simp [rightStreamTape, preservingReadMachine, TM.step,
            Tape.write, Tape.move, List.replicate_succ]
      rw [hs, ih (none :: left), replicate_none_cons k left]
      rfl

/-- Index 0 across a gap of `k` blanks. -/
theorem gapRead_zero
    (b : Bool) (witnessTail tail : BitString) (k : Nat)
    (suffix : List (Option Bool)) :
    gapReadMachine.run (k + 4) (gapReadConfig (b :: witnessTail) k 0 tail suffix) =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := List.replicate (k + 1) none ++ (tail.map some ++ suffix) } } := by
  have e := replicate_none_cons k (some b :: witnessTail.map some)
  have h1 : gapReadMachine.run 1 (gapReadConfig (b :: witnessTail) k 0 tail suffix) =
      { state := .finalSepNoMoved,
        tape := { left := List.replicate k none ++ (some b :: witnessTail.map some),
                  head := none,
                  right := none :: (tail.map some ++ suffix) } } := by
    simp only [gapReadConfig, gapReadTape, List.map_cons]
    rw [e]
    simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move]
  have h2 := finalSep_over_blanks k b (witnessTail.map some)
    (none :: (tail.map some ++ suffix))
  have h3 : gapReadMachine.run 2
      { state := .finalSepNoMoved,
        tape := { left := witnessTail.map some, head := some b,
                  right := List.replicate (k + 1) none ++
                    (none :: (tail.map some ++ suffix)) } } =
      { state := .halt b,
        tape := { left := (b :: witnessTail).map some, head := none,
                  right := List.replicate (k + 1) none ++
                    (tail.map some ++ suffix) } } := by
    have e2 := replicate_none_cons k (tail.map some ++ suffix)
    simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, e2]
  rw [show k + 4 = (1 + (k + 1)) + 2 by omega, run_add, run_add, h1, h2, h3]

/-- Successor index across a gap of `k` blanks: enters the moved phase with
moved prefix `[b]` and gap `k`. -/
theorem gapRead_start_successor
    (b : Bool) (witnessTail tail : BitString) (n k : Nat)
    (suffix : List (Option Bool)) :
    gapReadMachine.run (2 * k + 6)
      (gapReadConfig (b :: witnessTail) k (n + 1) tail suffix) =
      gapIdxConfig [b] witnessTail n tail k suffix := by
  obtain ⟨x, xs, hx⟩ : ∃ x xs, encodeNat n ++ tail = x :: xs := by
    cases n <;> exact ⟨_, _, rfl⟩
  have hidx : gapIdxConfig [b] witnessTail n tail k suffix =
      gapMovedConfig [b] witnessTail x xs k suffix := by
    cases n <;> simp_all [gapIdxConfig, encodeNat]
  rw [hidx]
  let W : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some x :: (xs.map some ++ suffix)
  have e := replicate_none_cons k (some b :: W)
  have h1 : gapReadMachine.run 1 (gapReadConfig (b :: witnessTail) k (n + 1) tail suffix) =
      { state := .advanceSep,
        tape := { left := List.replicate k none ++ (some b :: W),
                  head := none, right := none :: src } } := by
    simp only [gapReadConfig, gapReadTape, List.map_cons, hx]
    rw [e]
    simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, W, src]
  have h2 := advanceSep_over_blanks k b W (none :: src)
  have e2 := replicate_none_cons k src
  have h3 : gapReadMachine.run 1
      { state := .advanceSep,
        tape := { left := W, head := some b,
                  right := List.replicate (k + 1) none ++ (none :: src) } } =
      { state := .writeMoved b,
        tape := { left := none :: W, head := none,
                  right := List.replicate k none ++ (none :: src) } } := by
    simp [gapReadMachine, preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ]
  -- from here on the machine is in the moved phase: transfer
  have h4 : preservingReadMachine.run 2
      { state := .writeMoved b,
        tape := { left := none :: W, head := none,
                  right := List.replicate k none ++ (none :: src) } } =
      { state := .returnBlanks,
        tape := rightStreamTape (none :: some b :: none :: W)
          (List.replicate k none ++ src) } := by
    rw [e2]
    cases k <;>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move,
        rightStreamTape, List.replicate_succ, src]
  have h5 := returnBlanks_stream k x (none :: some b :: none :: W)
    (xs.map some ++ suffix)
  let Cend : Configuration PreservingReadState (Option Bool) :=
    { state := .indexMoved,
      tape := { left := List.replicate k none ++ (none :: some b :: none :: W),
                head := some x, right := xs.map some ++ suffix } }
  have h45 : gapReadMachine.run (2 + (k + 1))
      { state := .writeMoved b,
        tape := { left := none :: W, head := none,
                  right := List.replicate k none ++ (none :: src) } } = Cend := by
    rw [gap_run_eq_preserving _ _ rfl, run_add, h4]
    simpa [src, Cend] using h5
  have hend : Cend = gapMovedConfig [b] witnessTail x xs k suffix := by
    simp only [Cend, gapMovedConfig, gapMovedTape, List.length_singleton,
      List.map_cons, List.map_nil, W]
    rw [replicate_none_cons k (some b :: none :: witnessTail.map some)]
    rw [show 1 + k = k + 1 by omega, List.replicate_succ]
    simp [List.append_assoc]
  have g2 : gapReadMachine.run (1 + (k + 1))
      (gapReadConfig (b :: witnessTail) k (n + 1) tail suffix) =
      { state := .advanceSep,
        tape := { left := W, head := some b,
                  right := List.replicate (k + 1) none ++ (none :: src) } } := by
    rw [run_add, h1, h2]
  have g3 : gapReadMachine.run ((1 + (k + 1)) + 1)
      (gapReadConfig (b :: witnessTail) k (n + 1) tail suffix) =
      { state := .writeMoved b,
        tape := { left := none :: W, head := none,
                  right := List.replicate k none ++ (none :: src) } } := by
    rw [run_add, g2, h3]
  have g4 : gapReadMachine.run (((1 + (k + 1)) + 1) + (2 + (k + 1)))
      (gapReadConfig (b :: witnessTail) k (n + 1) tail suffix) = Cend := by
    rw [run_add, g3, h45]
  rw [show 2 * k + 6 = ((1 + (k + 1)) + 1) + (2 + (k + 1)) by omega, g4, hend]

/-! ## 7. Complete gap-tolerant read for every in-range index -/

def gapReadFuel (k : Nat) : Nat → Nat
  | 0 => k + 4
  | n + 1 => (2 * k + 6) + gapMovedFuel 1 k n

/-- **Gap-tolerant preserving read.**  From the gapped layout (witness,
separator, `k` gap blanks, unary index `i`, source tail, arbitrary suffix), the
fixed finite-control `gapReadMachine` halts in `halt (witness.getD i false)`,
restores the witness exactly, blanks the `i + 1` index cells and preserves the
tail and suffix. -/
theorem gapRead_forall
    (witness tail : BitString) (k i : Nat) (suffix : List (Option Bool))
    (hi : i < witness.length) :
    gapReadMachine.run (gapReadFuel k i) (gapReadConfig witness k i tail suffix) =
      { state := .halt (witness.getD i false),
        tape :=
          { left := witness.map some,
            head := none,
            right := List.replicate (k + i + 1) none ++ (tail.map some ++ suffix) } } := by
  cases witness with
  | nil => simp at hi
  | cons b witnessTail =>
      cases i with
      | zero =>
          simpa [gapReadFuel] using gapRead_zero b witnessTail tail k suffix
      | succ n =>
          have hn : n < witnessTail.length := by simpa using hi
          rw [show gapReadFuel k (n + 1) = (2 * k + 6) + gapMovedFuel 1 k n from rfl,
            run_add, gapRead_start_successor]
          have hmp : movedPhase (gapIdxConfig [b] witnessTail n tail k suffix).state
              = true := by
            cases n <;> rfl
          rw [gap_run_eq_preserving _ _ hmp]
          have := gapMoved_forall b [] witnessTail tail k suffix n hn
          simp only [List.length_singleton] at this
          rw [this]
          simp [List.getD_cons_succ]
          omega

theorem gapRead_forall_value
    (witness tail : BitString) (k i : Nat) (suffix : List (Option Bool))
    (hi : i < witness.length) :
    (gapReadMachine.run (gapReadFuel k i)
      (gapReadConfig witness k i tail suffix)).state =
      .halt (witness.getD i false) := by
  rw [gapRead_forall witness tail k i suffix hi]

/-! ## 8. Polynomial fuel bound -/

theorem gapMovedFuel_le (m g n : Nat) :
    gapMovedFuel m g n ≤ (4 * (m + n) + 2 * g + 6) * n + 5 * (m + n) + g + 6 := by
  induction n generalizing m with
  | zero => simp [gapMovedFuel]
  | succ n ih =>
      simp only [gapMovedFuel]
      have h := ih (m + 1)
      rw [show m + 1 + n = m + (n + 1) by omega] at h
      have h2 : (4 * (m + (n + 1)) + 2 * g + 6) * n + 5 * (m + (n + 1)) + g + 6 +
          (4 * m + 2 * g + 6) ≤
          (4 * (m + (n + 1)) + 2 * g + 6) * (n + 1) + 5 * (m + (n + 1)) + g + 6 := by
        rw [Nat.mul_succ]
        omega
      omega

/-- The gap-tolerant read of index `i` across a gap of `k` blanks costs at most
`6 * (k + i + 2) * (k + i + 2)` steps (quadratic). -/
theorem gapReadFuel_le (k i : Nat) :
    gapReadFuel k i ≤ 6 * ((k + i + 2) * (k + i + 2)) := by
  cases i with
  | zero =>
      simp only [gapReadFuel]
      have : k + 2 ≤ (k + 0 + 2) * (k + 0 + 2) := by
        simp only [Nat.add_zero]
        have := Nat.mul_le_mul (Nat.le_refl (k + 2)) (show 1 ≤ k + 2 by omega)
        simpa using this
      omega
  | succ n =>
      simp only [gapReadFuel]
      have h := gapMovedFuel_le 1 k n
      have e1 : (4 * (1 + n) + 2 * k + 6) * n =
          4 * (n * n) + 2 * (k * n) + 10 * n := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
        (try rw [Nat.mul_comm n k])
        omega
      have e2 : (k + (n + 1) + 2) * (k + (n + 1) + 2) =
          k * k + 2 * (k * n) + n * n + 6 * k + 6 * n + 9 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        (try rw [Nat.mul_comm n k])
        omega
      rw [e2]
      omega

#print axioms MCore.Real.P01GapPreservingRead.gap_run_eq_preserving
#print axioms MCore.Real.P01GapPreservingRead.gapMoved_cycle
#print axioms MCore.Real.P01GapPreservingRead.gapMoved_false_finalize
#print axioms MCore.Real.P01GapPreservingRead.gapMoved_forall
#print axioms MCore.Real.P01GapPreservingRead.gapRead_zero
#print axioms MCore.Real.P01GapPreservingRead.gapRead_start_successor
#print axioms MCore.Real.P01GapPreservingRead.gapRead_forall
#print axioms MCore.Real.P01GapPreservingRead.gapRead_forall_value
#print axioms MCore.Real.P01GapPreservingRead.gapMovedFuel_le
#print axioms MCore.Real.P01GapPreservingRead.gapReadFuel_le

end P01GapPreservingRead
end Real
end MCore
