import MCore.Real.P01WitnessIndexedReadPreserving

namespace MCore
namespace Real
namespace P01WitnessIndexedReadGap

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01WitnessIndexedReadPreserving

/-- Direct source-bit view of the preserving reader with an arbitrary physical
blank gap between the source cursor and the witness/source separator. -/
def gapReadBitsTape
    (witness : BitString) (gap : Nat) (source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := none,
        right := [] }
  | b :: bs =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := some b,
        right := bs.map some }

/-- Unary-index specialization of the gap-aware input layout. -/
def preservingReadGapTape
    (witness : BitString) (gap i : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  gapReadBitsTape witness gap (encodeNat i ++ tail)

/-- Direct moved-prefix representation with the original cursor gap retained.
Each consumed unary marker contributes one additional blank on top of `gap`. -/
def movedGapBitsTape
    (gap : Nat) (moved rest source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left :=
          List.replicate (gap + moved.length) none ++
            moved.map some ++ (none :: rest.map some),
        head := none,
        right := [] }
  | x :: xs =>
      { left :=
          List.replicate (gap + moved.length) none ++
            moved.map some ++ (none :: rest.map some),
        head := some x,
        right := xs.map some }

def movedGapBitsConfig
    (gap : Nat) (moved rest source : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := movedGapBitsTape gap moved rest source }

def preservingMovedGapConfig
    (gap : Nat) (moved rest : BitString) (n : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  movedGapBitsConfig gap moved rest (encodeNat n ++ tail)

@[simp] theorem preservingReadGapTape_zero_gap
    (witness : BitString) (i : Nat) (tail : BitString) :
    preservingReadGapTape witness 0 i tail =
      preservingReadTape witness i tail := by
  cases i <;> rfl

/-- The modified initial-advance state crosses any finite block of physical
blanks and captures the first witness bit. -/
theorem advanceSep_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .advanceSep,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .writeMoved b,
        tape :=
          { left := none :: left,
            head := none,
            right := List.replicate k none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.advanceSep) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .advanceSep,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .writeMoved b,
          tape :=
            { left := none :: left,
              head := none,
              right := List.replicate (Nat.succ k) none ++ right } }
      rw [ih (none :: right)]
      congr 2
      exact replicate_none_cons k right

/-- Final zero-index scan across an arbitrary cursor gap. -/
theorem finalSepNoMoved_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .finalSepNoMoved,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .restoreHalt b,
        tape :=
          { left := some b :: left,
            head := none,
            right := List.replicate k none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.finalSepNoMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .finalSepNoMoved,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .restoreHalt b,
          tape :=
            { left := some b :: left,
              head := none,
              right := List.replicate (Nat.succ k) none ++ right } }
      rw [ih (none :: right)]
      congr 2
      exact replicate_none_cons k right

/-- `returnBlanks` starting from a stream view. -/
theorem returnBlanks_from_stream
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .returnBlanks,
        tape :=
          rightStreamTape left
            (List.replicate k none ++ (some b :: right)) } =
      { state := .indexMoved,
        tape :=
          { left := List.replicate k none ++ left,
            head := some b,
            right := right } } := by
  cases k with
  | zero =>
      simp [rightStreamTape, preservingReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | succ k =>
      simpa [rightStreamTape, List.replicate_succ, List.append_assoc] using
        returnBlanks_over_blanks k b left right

/-- Gap-aware zero-index read.  The witness is unchanged and all pre-existing
cursor blanks remain to the right of the canonical witness/source separator. -/
theorem preservingReadGap_zero
    (b : Bool) (witnessTail tail : BitString) (gap : Nat) :
    preservingReadMachine.run (gap + 4)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape (b :: witnessTail) gap 0 tail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := List.replicate (gap + 1) none ++ tail.map some } } := by
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := preservingReadGapTape (b :: witnessTail) gap 0 tail }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSepNoMoved,
      tape :=
        { left := List.replicate gap none ++ (some b :: witnessTail.map some),
          head := none,
          right := none :: tail.map some } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .restoreHalt b,
      tape :=
        { left := some b :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: tail.map some) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt b,
      tape :=
        { left := (b :: witnessTail).map some,
          head := none,
          right := List.replicate (gap + 1) none ++ tail.map some } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, preservingReadGapTape, gapReadBitsTape]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, encodeNat, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSepNoMoved_over_blanks gap b (witnessTail.map some)
        (none :: tail.map some)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    rw [replicate_none_cons gap (tail.map some)]
    simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

  rw [show gap + 4 = 1 + ((gap + 2) + 1) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  simpa [C3] using h23

/-- One first-successor cycle on a direct source beginning in `true`. -/
theorem preservingReadGap_start_true
    (b next : Bool) (witnessTail sourceTail : BitString) (gap : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape :=
          gapReadBitsTape (b :: witnessTail) gap
            (true :: next :: sourceTail) } =
      movedGapBitsConfig gap [b] witnessTail (next :: sourceTail) := by
  let src : List (Option Bool) := some next :: sourceTail.map some
  let L : List (Option Bool) := some b :: none :: witnessTail.map some
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := gapReadBitsTape (b :: witnessTail) gap
        (true :: next :: sourceTail) }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .advanceSep,
      tape :=
        { left := List.replicate gap none ++
            (some b :: witnessTail.map some),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .writeMoved b,
      tape :=
        { left := none :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnMoved,
      tape :=
        rightStreamTape L
          (List.replicate gap none ++ (none :: src)) }
  let after : List (Option Bool) :=
    List.replicate gap none ++ src
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape (none :: L) after }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    movedGapBitsConfig gap [b] witnessTail (next :: sourceTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, gapReadBitsTape, src]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      advanceSep_over_blanks gap b (witnessTail.map some) (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3, L, src, rightStreamTape]
    cases gap <;>
      simp [preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h34 : preservingReadMachine.run 1 C3 = C4 := by
    dsimp [C3, C4, L, after, src]
    have hrep :=
      replicate_none_cons gap (some next :: sourceTail.map some)
    rw [show List.replicate gap none ++
        (none :: some next :: sourceTail.map some) =
        none :: (List.replicate gap none ++
          (some next :: sourceTail.map some)) by
      simpa using hrep]
    simpa [returnMovedTape] using
      returnMoved_over_bits ([] : BitString) L after

  have h45 : preservingReadMachine.run (gap + 1) C4 = C5 := by
    dsimp [C4, C5, after, L, src, movedGapBitsConfig, movedGapBitsTape]
    have h :=
      returnBlanks_from_stream gap next
        (none :: some b :: none :: witnessTail.map some)
        (sourceTail.map some)
    rw [h]
    congr 2
    have hr :=
      replicate_none_cons gap
        (some b :: none :: witnessTail.map some)
    simpa [List.replicate_succ, List.append_assoc] using hr

  rw [show 2 * gap + 6 =
      1 + ((gap + 2) + (1 + (1 + (gap + 1)))) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  rw [run_add, h23]
  rw [run_add, h34]
  exact h45

/-- Unary successor specialization of the first gap-aware cycle. -/
theorem preservingReadGap_start_successor
    (b : Bool) (witnessTail tail : BitString) (gap n : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape (b :: witnessTail) gap (n + 1) tail } =
      preservingMovedGapConfig gap [b] witnessTail n tail := by
  cases n with
  | zero =>
      simpa [preservingReadGapTape, preservingMovedGapConfig,
        gapReadBitsTape, encodeNat, List.append_assoc] using
        preservingReadGap_start_true b false witnessTail tail gap
  | succ n =>
      simpa [preservingReadGapTape, preservingMovedGapConfig,
        gapReadBitsTape, encodeNat, List.append_assoc] using
        preservingReadGap_start_true b true witnessTail
          (encodeNat n ++ tail) gap


/-- One complete successor cycle with an arbitrary pre-existing physical gap. -/
theorem preservingMovedGap_cycle
    (first b next : Bool)
    (movedTail witnessTail sourceTail : BitString)
    (gap : Nat) :
    preservingReadMachine.run
      (2 * gap + 4 * movedTail.length + 10)
      (movedGapBitsConfig gap
        (first :: movedTail) (b :: witnessTail)
        (true :: next :: sourceTail)) =
      movedGapBitsConfig gap
        ((first :: movedTail) ++ [b]) witnessTail
        (next :: sourceTail) := by
  let m : Nat := movedTail.length
  let k : Nat := gap + m
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate k none ++ (none :: src)
  let stream : List (Option Bool) :=
    moved.reverse.map some ++ (none :: after)
  let restoredLeft : List (Option Bool) :=
    none :: (moved.map some ++ (some b :: none :: witnessSuffix))

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedGapBitsConfig gap moved (b :: witnessTail)
      (true :: next :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekMoved,
      tape :=
        { left :=
            List.replicate k none ++
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
          right := List.replicate (k + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .scanMoved,
      tape :=
        scanMovedTape movedTail b witnessSuffix
          (some first ::
            (List.replicate (k + 1) none ++ (none :: src))) }
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
          right := List.replicate k none ++ src } }
  let C7e : Configuration PreservingReadState (Option Bool) :=
    { state := .indexMoved,
      tape :=
        { left := List.replicate (k + 1) none ++ restoredLeft,
          head := some next,
          right := sourceTail.map some } }
  let C7 : Configuration PreservingReadState (Option Bool) :=
    movedGapBitsConfig gap (moved ++ [b]) witnessTail
      (next :: sourceTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, k, witnessSuffix, src,
      movedGapBitsConfig, movedGapBitsTape]
    rw [show gap + (List.length movedTail + 1) =
        (gap + List.length movedTail) + 1 by omega]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (k + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      seekMoved_over_blanks k first
        (movedTail.map some ++ (none :: some b :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      seekMoved_step_bit first b movedTail witnessSuffix
        (List.replicate (k + 1) none ++ (none :: src))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, stream, moved, after, src, m, k]
    simpa [List.reverse_cons, List.map_append,
      List.replicate_succ, List.append_assoc] using
      scanMoved_over_bits movedTail b witnessSuffix
        (some first ::
          (List.replicate (gap + movedTail.length + 1) none ++
            (none :: (some next :: sourceTail.map some))))

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
      (rightStreamTape_blank_block k restoredLeft src)

  have h67 : preservingReadMachine.run (k + 2) C6e = C7e := by
    dsimp [C6e, C7e, src]
    simpa using
      returnBlanks_over_blanks k next restoredLeft (sourceTail.map some)

  have h7eq : C7e = C7 := by
    have hcount :
        gap + ((movedTail ++ [b]).length + 1) =
          (gap + movedTail.length) + 2 := by
      simp
      omega
    dsimp [C7e, C7, movedGapBitsConfig, movedGapBitsTape,
      restoredLeft, moved, m, k, src]
    rw [hcount]
    simp [List.replicate_succ, List.map_append, List.append_assoc]
    exact replicate_none_cons
      (gap + movedTail.length)
      (some first ::
        (movedTail.map some ++ some b :: none :: witnessSuffix))

  have h56e : preservingReadMachine.run (m + 2) C5 = C6e := by
    rw [h56, h6eq]

  have h67t : preservingReadMachine.run (k + 2) C6e = C7 := by
    rw [h67, h7eq]

  have h02 :
      preservingReadMachine.run (1 + (k + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingReadMachine.run ((1 + (k + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (k + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run
        ((((1 + (k + 1)) + 1) + (m + 1)) + 2) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (k + 1)) + 1) + (m + 1)) + 2) + (m + 2)) C0 = C6e := by
    rw [run_add, h05, h56e]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (k + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (k + 2)) C0 =
        C7 := by
    rw [run_add, h06, h67t]

  have hFuel :
      2 * gap + 4 * movedTail.length + 10 =
        ((((((1 + (k + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (k + 2)) := by
    dsimp [m, k]
    omega
  rw [hFuel]
  simpa [C0, C7, moved] using h07

/-- Gap-aware terminal false case after a nonempty prefix has been moved. -/
def preservingMovedGapFinalizeFuel (gap : Nat) (moved : BitString) : Nat :=
  gap + 5 * moved.length + 6

theorem movedGapBits_false_finalize
    (first selected : Bool)
    (movedTail rest sourceTail : BitString)
    (gap : Nat) :
    preservingReadMachine.run
      (preservingMovedGapFinalizeFuel gap (first :: movedTail))
      (movedGapBitsConfig gap
        (first :: movedTail) (selected :: rest)
        (false :: sourceTail)) =
      { state := .halt selected,
        tape :=
          { left := ((first :: movedTail) ++ (selected :: rest)).map some,
            head := none,
            right :=
              List.replicate
                (gap + (first :: movedTail).length + 1) none ++
                sourceTail.map some } } := by
  let m : Nat := movedTail.length
  let k : Nat := gap + m
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := rest.map some
  let src : List (Option Bool) := sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate (k + 1) none ++ (none :: src)

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedGapBitsConfig gap moved (selected :: rest)
      (false :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            List.replicate k none ++
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
          right := List.replicate (k + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalScanMoved,
      tape :=
        scanMovedTape movedTail selected witnessSuffix
          (some first ::
            (List.replicate (k + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalReadMoved,
      tape :=
        { left := witnessSuffix,
          head := some selected,
          right :=
            none :: (moved.reverse.map some ++ after) } }
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
          right := List.replicate (k + 2) none ++ src } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, k, witnessSuffix, src,
      movedGapBitsConfig, movedGapBitsTape]
    rw [show gap + (List.length movedTail + 1) =
        (gap + List.length movedTail) + 1 by omega]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (k + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSeekMoved_over_blanks k first
        (movedTail.map some ++ (none :: some selected :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      finalSeekMoved_step_bit first selected movedTail witnessSuffix
        (List.replicate (k + 1) none ++ (none :: src))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, moved, after, src, m, k]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      finalScanMoved_over_bits movedTail selected witnessSuffix
        (some first ::
          (List.replicate (gap + movedTail.length + 1) none ++
            (none :: sourceTail.map some)))

  have h45 : preservingReadMachine.run 1 C4 = C5 := by
    dsimp [C4, C5, moved, after, src, witnessSuffix, restoreMovedConfig]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.reverse_cons, List.map_append,
      List.append_assoc]

  have h56 :
      preservingReadMachine.run (3 * moved.length) C5 = C6 := by
    dsimp [C5, C6, restoredWitness]
    simpa [moved] using
      restoreMoved_over_bits selected moved.reverse
        (some selected :: witnessSuffix) after

  have h67 : preservingReadMachine.run 3 C6 = C7 := by
    dsimp [C6, C7, restoreMovedConfig, restoredWitness,
      after, src, moved, m, k]
    have hr :=
      replicate_none_cons
        (gap + movedTail.length) (sourceTail.map some)
    simpa [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ,
      List.map_append, List.append_assoc] using hr

  have h02 :
      preservingReadMachine.run (1 + (k + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingReadMachine.run ((1 + (k + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (k + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run
        ((((1 + (k + 1)) + 1) + (m + 1)) + 1) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (k + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) C0 = C6 := by
    rw [run_add, h05, h56]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (k + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) + 3) C0 = C7 := by
    rw [run_add, h06, h67]

  have hFuel :
      preservingMovedGapFinalizeFuel gap moved =
        ((((((1 + (k + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) + 3) := by
    dsimp [preservingMovedGapFinalizeFuel, moved, m, k]
    omega
  rw [show preservingMovedGapFinalizeFuel gap (first :: movedTail) =
      preservingMovedGapFinalizeFuel gap moved by rfl]
  rw [hFuel]
  simpa [C0, C7, moved, restoredWitness, src, m, k,
    List.map_append, List.append_assoc] using h07

/-- Unary-index form of one gap-aware successor cycle. -/
theorem preservingMovedGap_cycle_index
    (first next : Bool) (movedTail rest tail : BitString)
    (gap n : Nat) :
    preservingReadMachine.run
      (2 * gap + 4 * movedTail.length + 10)
      (preservingMovedGapConfig gap
        (first :: movedTail) (next :: rest) (n + 1) tail) =
      preservingMovedGapConfig gap
        ((first :: movedTail) ++ [next]) rest n tail := by
  cases n with
  | zero =>
      simpa [preservingMovedGapConfig, encodeNat, List.append_assoc] using
        preservingMovedGap_cycle first next false movedTail rest tail gap
  | succ n =>
      simpa [preservingMovedGapConfig, encodeNat, List.append_assoc] using
        preservingMovedGap_cycle first next true movedTail rest
          (encodeNat n ++ tail) gap



/-- Exact remaining fuel from a nonempty moved prefix in the gap-aware layout. -/
def preservingMovedGapFuel (gap movedLen : Nat) : Nat → Nat
  | 0 => gap + 5 * movedLen + 6
  | n + 1 =>
      (2 * gap + 4 * movedLen + 6) +
        preservingMovedGapFuel gap (movedLen + 1) n

/-- Complete read from the gap-aware moved-prefix invariant. -/
theorem preservingMovedGap_forall
    (first : Bool) (movedTail rest tail : BitString)
    (gap n : Nat)
    (h : n < rest.length) :
    preservingReadMachine.run
      (preservingMovedGapFuel gap (first :: movedTail).length n)
      (preservingMovedGapConfig gap (first :: movedTail) rest n tail) =
      { state := .halt (rest.getD n false),
        tape :=
          { left := ((first :: movedTail) ++ rest).map some,
            head := none,
            right :=
              List.replicate
                (gap + (first :: movedTail).length + n + 1) none ++
                tail.map some } } := by
  induction n generalizing movedTail rest with
  | zero =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          dsimp [preservingMovedGapFuel]
          simpa [preservingMovedGapConfig, encodeNat,
            preservingMovedGapFinalizeFuel,
            List.map_append, List.append_assoc] using
            movedGapBits_false_finalize
              first selected movedTail restTail tail gap
  | succ n ih =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          have htail : n < restTail.length := by
            simpa using h
          rw [show
            preservingMovedGapFuel gap (first :: movedTail).length (n + 1) =
              (2 * gap + 4 * movedTail.length + 10) +
                preservingMovedGapFuel gap
                  (first :: (movedTail ++ [selected])).length n by
              simp [preservingMovedGapFuel]
              omega]
          rw [run_add]
          rw [preservingMovedGap_cycle_index
            first selected movedTail restTail tail gap n]
          change preservingReadMachine.run
            (preservingMovedGapFuel gap
              (first :: (movedTail ++ [selected])).length n)
            (preservingMovedGapConfig gap
              (first :: (movedTail ++ [selected])) restTail n tail) = _
          rw [ih (movedTail := movedTail ++ [selected])
            (rest := restTail) htail]
          simp [List.getD_cons_succ, List.map_append,
            List.append_assoc]
          omega

/-- Exact full-run fuel from the gap-aware initial layout. -/
def preservingReadGapFuel (gap : Nat) : Nat → Nat
  | 0 => gap + 4
  | n + 1 =>
      (2 * gap + 6) + preservingMovedGapFuel gap 1 n

/-- Complete preserving indexed read for every valid index and every physical
blank gap between the source cursor and the witness separator. -/
theorem preservingReadGap_forall
    (i : Nat) (witness tail : BitString)
    (gap : Nat)
    (h : i < witness.length) :
    preservingReadMachine.run (preservingReadGapFuel gap i)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape witness gap i tail } =
      { state := .halt (witness.getD i false),
        tape :=
          { left := witness.map some,
            head := none,
            right :=
              List.replicate (gap + i + 1) none ++ tail.map some } } := by
  cases i with
  | zero =>
      cases witness with
      | nil =>
          simp at h
      | cons b witnessTail =>
          simpa [preservingReadGapFuel, List.getD_cons_zero] using
            preservingReadGap_zero b witnessTail tail gap
  | succ n =>
      cases witness with
      | nil =>
          simp at h
      | cons b witnessTail =>
          have htail : n < witnessTail.length := by
            simpa using h
          rw [show preservingReadGapFuel gap (n + 1) =
              (2 * gap + 6) + preservingMovedGapFuel gap 1 n by rfl]
          rw [run_add]
          rw [preservingReadGap_start_successor
            b witnessTail tail gap n]
          have hm :=
            preservingMovedGap_forall b [] witnessTail tail gap n htail
          simpa [List.getD_cons_succ, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hm

theorem preservingReadGap_forall_value
    (i : Nat) (witness tail : BitString)
    (gap : Nat)
    (h : i < witness.length) :
    (preservingReadMachine.run (preservingReadGapFuel gap i)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape witness gap i tail }).state =
      .halt (witness.getD i false) := by
  rw [preservingReadGap_forall i witness tail gap h]


/-- Quadratic envelope for the gap-aware moved-prefix fuel. -/
theorem preservingMovedGapFuel_le (gap m n : Nat) :
    preservingMovedGapFuel gap m n ≤
      (2 * gap + 4 * (m + n) + 6) * n +
        gap + 5 * (m + n) + 6 := by
  induction n generalizing m with
  | zero =>
      simp [preservingMovedGapFuel]
  | succ n ih =>
      simp only [preservingMovedGapFuel]
      have h := ih (m + 1)
      rw [show m + 1 + n = m + (n + 1) by omega] at h
      have hcost :
          2 * gap + 4 * m + 6 ≤
            2 * gap + 4 * (m + (n + 1)) + 6 := by
        omega
      have hstep :
          (2 * gap + 4 * (m + (n + 1)) + 6) * n +
              gap + 5 * (m + (n + 1)) + 6 +
              (2 * gap + 4 * m + 6) ≤
            (2 * gap + 4 * (m + (n + 1)) + 6) * (n + 1) +
              gap + 5 * (m + (n + 1)) + 6 := by
        rw [Nat.mul_succ]
        omega
      omega

/-- Explicit quadratic envelope for a complete preserving read with an
arbitrary physical cursor gap. -/
theorem preservingReadGapFuel_le (gap i : Nat) :
    preservingReadGapFuel gap i ≤
      (2 * gap + 4 * (i + 1) + 6) * i +
        3 * gap + 5 * (i + 1) + 12 := by
  cases i with
  | zero =>
      simp [preservingReadGapFuel]
      omega
  | succ n =>
      simp only [preservingReadGapFuel]
      have h := preservingMovedGapFuel_le gap 1 n
      have hcoef :
          2 * gap + 4 * (1 + n) + 6 ≤
            2 * gap + 4 * ((n + 1) + 1) + 6 := by
        omega
      have hmul :
          (2 * gap + 4 * (1 + n) + 6) * n ≤
            (2 * gap + 4 * ((n + 1) + 1) + 6) * n := by
        exact Nat.mul_le_mul_right n hcoef
      rw [Nat.mul_succ]
      omega

#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingMovedGap_forall
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_forall
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_forall_value
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingMovedGapFuel_le
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGapFuel_le


#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_zero
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_start_successor

end P01WitnessIndexedReadGap
end Real
end MCore
