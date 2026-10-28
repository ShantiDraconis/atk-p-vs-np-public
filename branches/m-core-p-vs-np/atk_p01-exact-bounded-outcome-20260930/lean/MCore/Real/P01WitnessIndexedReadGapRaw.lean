import MCore.Real.P01WitnessIndexedReadGap

namespace MCore
namespace Real
namespace P01WitnessIndexedReadGapRaw

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01WitnessIndexedReadPreserving
open P01WitnessIndexedReadGap

/-- Raw-symbol source view.  Unlike \`gapReadBitsTape\`, the suffix may contain
physical separator blanks, frame bits, and padding. -/
def gapReadRawTape
    (witness : BitString) (gap : Nat)
    (source : List (Option Bool)) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := none,
        right := [] }
  | x :: xs =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := x,
        right := xs }

/-- Canonical unary index followed by an arbitrary physical suffix. -/
def preservingReadGapRawTape
    (witness : BitString) (gap i : Nat)
    (rawTail : List (Option Bool)) :
    Tape (Option Bool) :=
  gapReadRawTape witness gap ((encodeNat i).map some ++ rawTail)

/-- Moved-prefix view with an arbitrary physical source suffix. -/
def movedGapRawBitsTape
    (gap : Nat) (moved rest : BitString)
    (source : List (Option Bool)) :
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
        head := x,
        right := xs }

def movedGapRawBitsConfig
    (gap : Nat) (moved rest : BitString)
    (source : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := movedGapRawBitsTape gap moved rest source }

def preservingMovedGapRawConfig
    (gap : Nat) (moved rest : BitString)
    (n : Nat) (rawTail : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  movedGapRawBitsConfig gap moved rest
    ((encodeNat n).map some ++ rawTail)

/-- Compatibility with the already-certified bit-only gap layout. -/
theorem preservingReadGapRawTape_bits
    (witness tail : BitString) (gap i : Nat) :
    preservingReadGapRawTape witness gap i (tail.map some) =
      preservingReadGapTape witness gap i tail := by
  cases i <;>
    simp [preservingReadGapRawTape, preservingReadGapTape,
      gapReadRawTape, gapReadBitsTape, encodeNat,
      List.map_append, List.append_assoc]

/-- Gap-aware zero-index read with an arbitrary physical suffix. -/
theorem preservingReadGapRaw_zero
    (b : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool)) (gap : Nat) :
    preservingReadMachine.run (gap + 4)
      { state := preservingReadMachine.initial,
        tape :=
          preservingReadGapRawTape
            (b :: witnessTail) gap 0 rawTail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := List.replicate (gap + 1) none ++ rawTail } } := by
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := preservingReadGapRawTape
        (b :: witnessTail) gap 0 rawTail }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSepNoMoved,
      tape :=
        { left := List.replicate gap none ++
            (some b :: witnessTail.map some),
          head := none,
          right := none :: rawTail } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .restoreHalt b,
      tape :=
        { left := some b :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: rawTail) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt b,
      tape :=
        { left := (b :: witnessTail).map some,
          head := none,
          right := List.replicate (gap + 1) none ++ rawTail } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, preservingReadGapRawTape, gapReadRawTape]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, encodeNat, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSepNoMoved_over_blanks gap b
        (witnessTail.map some) (none :: rawTail)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    have hr := replicate_none_cons gap rawTail
    simpa [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ,
      List.append_assoc] using hr

  rw [show gap + 4 = 1 + ((gap + 2) + 1) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  simpa [C3] using h23

/-- First true unary marker with arbitrary physical suffix after the next unary
symbol. -/
theorem preservingReadGapRaw_start_true
    (b next : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool)) (gap : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape :=
          gapReadRawTape (b :: witnessTail) gap
            (some true :: some next :: rawTail) } =
      movedGapRawBitsConfig gap [b] witnessTail
        (some next :: rawTail) := by
  let src : List (Option Bool) := some next :: rawTail
  let L : List (Option Bool) := some b :: none :: witnessTail.map some
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := gapReadRawTape (b :: witnessTail) gap
        (some true :: some next :: rawTail) }
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
      tape := rightStreamTape L
        (List.replicate gap none ++ (none :: src)) }
  let after : List (Option Bool) :=
    List.replicate gap none ++ src
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape (none :: L) after }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    movedGapRawBitsConfig gap [b] witnessTail
      (some next :: rawTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, gapReadRawTape, src]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      advanceSep_over_blanks gap b
        (witnessTail.map some) (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3, L, src, rightStreamTape]
    cases gap <;>
      simp [preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ,
        List.append_assoc]

  have h34 : preservingReadMachine.run 1 C3 = C4 := by
    dsimp [C3, C4, L, after, src]
    have hrep := replicate_none_cons gap (some next :: rawTail)
    rw [show List.replicate gap none ++
        (none :: some next :: rawTail) =
        none :: (List.replicate gap none ++
          (some next :: rawTail)) by simpa using hrep]
    simpa [returnMovedTape] using
      returnMoved_over_bits ([] : BitString) L after

  have h45 : preservingReadMachine.run (gap + 1) C4 = C5 := by
    dsimp [C4, C5, after, L, src,
      movedGapRawBitsConfig, movedGapRawBitsTape]
    have h :=
      returnBlanks_from_stream gap next
        (none :: some b :: none :: witnessTail.map some) rawTail
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

/-- Unary successor specialization with a raw suffix. -/
theorem preservingReadGapRaw_start_successor
    (b : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool))
    (gap n : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapRawTape
          (b :: witnessTail) gap (n + 1) rawTail } =
      preservingMovedGapRawConfig gap [b] witnessTail n rawTail := by
  cases n with
  | zero =>
      simpa [preservingReadGapRawTape, preservingMovedGapRawConfig,
        gapReadRawTape, encodeNat, List.map_append,
        List.append_assoc] using
        preservingReadGapRaw_start_true
          b false witnessTail rawTail gap
  | succ n =>
      simpa [preservingReadGapRawTape, preservingMovedGapRawConfig,
        gapReadRawTape, encodeNat, List.map_append,
        List.append_assoc] using
        preservingReadGapRaw_start_true
          b true witnessTail
          ((encodeNat n).map some ++ rawTail) gap


/-- One complete moved-prefix successor cycle with an arbitrary physical
suffix. -/
theorem preservingMovedGapRaw_cycle
    (first b next : Bool)
    (movedTail witnessTail : BitString)
    (rawTail : List (Option Bool))
    (gap : Nat) :
    preservingReadMachine.run
      (2 * gap + 4 * movedTail.length + 10)
      (movedGapRawBitsConfig gap
        (first :: movedTail) (b :: witnessTail)
        (some true :: some next :: rawTail)) =
      movedGapRawBitsConfig gap
        ((first :: movedTail) ++ [b]) witnessTail
        (some next :: rawTail) := by
  let m : Nat := movedTail.length
  let k : Nat := gap + m
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: rawTail
  let after : List (Option Bool) :=
    List.replicate k none ++ (none :: src)
  let stream : List (Option Bool) :=
    moved.reverse.map some ++ (none :: after)
  let restoredLeft : List (Option Bool) :=
    none :: (moved.map some ++ (some b :: none :: witnessSuffix))

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedGapRawBitsConfig gap moved (b :: witnessTail)
      (some true :: some next :: rawTail)
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
          right := rawTail } }
  let C7 : Configuration PreservingReadState (Option Bool) :=
    movedGapRawBitsConfig gap (moved ++ [b]) witnessTail
      (some next :: rawTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, k, witnessSuffix, src,
      movedGapRawBitsConfig, movedGapRawBitsTape]
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
            (none :: (some next :: rawTail))))

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
      returnBlanks_over_blanks k next restoredLeft rawTail

  have h7eq : C7e = C7 := by
    have hcount :
        gap + ((movedTail ++ [b]).length + 1) =
          (gap + movedTail.length) + 2 := by
      simp
      omega
    dsimp [C7e, C7, movedGapRawBitsConfig, movedGapRawBitsTape,
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

/-- Terminal false marker with an arbitrary raw suffix. -/
theorem movedGapRawBits_false_finalize
    (first selected : Bool)
    (movedTail rest : BitString)
    (rawTail : List (Option Bool))
    (gap : Nat) :
    preservingReadMachine.run
      (preservingMovedGapFinalizeFuel gap (first :: movedTail))
      (movedGapRawBitsConfig gap
        (first :: movedTail) (selected :: rest)
        (some false :: rawTail)) =
      { state := .halt selected,
        tape :=
          { left := ((first :: movedTail) ++ (selected :: rest)).map some,
            head := none,
            right :=
              List.replicate
                (gap + (first :: movedTail).length + 1) none ++
                rawTail } } := by
  let m : Nat := movedTail.length
  let k : Nat := gap + m
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := rest.map some
  let after : List (Option Bool) :=
    List.replicate (k + 1) none ++ (none :: rawTail)

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedGapRawBitsConfig gap moved (selected :: rest)
      (some false :: rawTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            List.replicate k none ++
              (some first ::
                (movedTail.map some ++
                  (none :: some selected :: witnessSuffix))),
          head := none,
          right := none :: rawTail } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            movedTail.map some ++ (none :: some selected :: witnessSuffix),
          head := some first,
          right := List.replicate (k + 1) none ++
            (none :: rawTail) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalScanMoved,
      tape :=
        scanMovedTape movedTail selected witnessSuffix
          (some first ::
            (List.replicate (k + 1) none ++ (none :: rawTail))) }
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
          right := List.replicate (k + 2) none ++ rawTail } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, k, witnessSuffix,
      movedGapRawBitsConfig, movedGapRawBitsTape]
    rw [show gap + (List.length movedTail + 1) =
        (gap + List.length movedTail) + 1 by omega]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (k + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSeekMoved_over_blanks k first
        (movedTail.map some ++ (none :: some selected :: witnessSuffix))
        (none :: rawTail)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      finalSeekMoved_step_bit first selected movedTail witnessSuffix
        (List.replicate (k + 1) none ++ (none :: rawTail))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, moved, after, m, k]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      finalScanMoved_over_bits movedTail selected witnessSuffix
        (some first ::
          (List.replicate (gap + movedTail.length + 1) none ++
            (none :: rawTail)))

  have h45 : preservingReadMachine.run 1 C4 = C5 := by
    dsimp [C4, C5, moved, after, witnessSuffix, restoreMovedConfig]
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
      after, moved, m, k]
    have hr :=
      replicate_none_cons
        (gap + movedTail.length) rawTail
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
  simpa [C0, C7, moved, restoredWitness, m, k,
    List.map_append, List.append_assoc] using h07

/-- Unary-index version of the raw-suffix successor cycle. -/
theorem preservingMovedGapRaw_cycle_index
    (first next : Bool) (movedTail rest : BitString)
    (rawTail : List (Option Bool))
    (gap n : Nat) :
    preservingReadMachine.run
      (2 * gap + 4 * movedTail.length + 10)
      (preservingMovedGapRawConfig gap
        (first :: movedTail) (next :: rest) (n + 1) rawTail) =
      preservingMovedGapRawConfig gap
        ((first :: movedTail) ++ [next]) rest n rawTail := by
  cases n with
  | zero =>
      simpa [preservingMovedGapRawConfig, encodeNat,
        List.map_append, List.append_assoc] using
        preservingMovedGapRaw_cycle
          first next false movedTail rest rawTail gap
  | succ n =>
      simpa [preservingMovedGapRawConfig, encodeNat,
        List.map_append, List.append_assoc] using
        preservingMovedGapRaw_cycle
          first next true movedTail rest
          ((encodeNat n).map some ++ rawTail) gap

/-- Complete moved-prefix read with arbitrary physical suffix. -/
theorem preservingMovedGapRaw_forall
    (first : Bool) (movedTail rest : BitString)
    (rawTail : List (Option Bool))
    (gap n : Nat)
    (h : n < rest.length) :
    preservingReadMachine.run
      (preservingMovedGapFuel gap (first :: movedTail).length n)
      (preservingMovedGapRawConfig gap
        (first :: movedTail) rest n rawTail) =
      { state := .halt (rest.getD n false),
        tape :=
          { left := ((first :: movedTail) ++ rest).map some,
            head := none,
            right :=
              List.replicate
                (gap + (first :: movedTail).length + n + 1) none ++
                rawTail } } := by
  induction n generalizing movedTail rest with
  | zero =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          dsimp [preservingMovedGapFuel]
          simpa [preservingMovedGapRawConfig, encodeNat,
            preservingMovedGapFinalizeFuel,
            List.map_append, List.append_assoc] using
            movedGapRawBits_false_finalize
              first selected movedTail restTail rawTail gap
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
          rw [preservingMovedGapRaw_cycle_index
            first selected movedTail restTail rawTail gap n]
          change preservingReadMachine.run
            (preservingMovedGapFuel gap
              (first :: (movedTail ++ [selected])).length n)
            (preservingMovedGapRawConfig gap
              (first :: (movedTail ++ [selected])) restTail n rawTail) = _
          rw [ih (movedTail := movedTail ++ [selected])
            (rest := restTail) htail]
          simp [List.getD_cons_succ, List.map_append,
            List.append_assoc]
          omega

/-- Full preserving indexed read with arbitrary physical suffix. -/
theorem preservingReadGapRaw_forall
    (i : Nat) (witness : BitString)
    (rawTail : List (Option Bool))
    (gap : Nat)
    (h : i < witness.length) :
    preservingReadMachine.run (preservingReadGapFuel gap i)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapRawTape witness gap i rawTail } =
      { state := .halt (witness.getD i false),
        tape :=
          { left := witness.map some,
            head := none,
            right :=
              List.replicate (gap + i + 1) none ++ rawTail } } := by
  cases i with
  | zero =>
      cases witness with
      | nil =>
          simp at h
      | cons b witnessTail =>
          simpa [preservingReadGapFuel, List.getD_cons_zero] using
            preservingReadGapRaw_zero b witnessTail rawTail gap
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
          rw [preservingReadGapRaw_start_successor
            b witnessTail rawTail gap n]
          have hm :=
            preservingMovedGapRaw_forall
              b [] witnessTail rawTail gap n htail
          simpa [List.getD_cons_succ, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hm

theorem preservingReadGapRaw_forall_value
    (i : Nat) (witness : BitString)
    (rawTail : List (Option Bool))
    (gap : Nat)
    (h : i < witness.length) :
    (preservingReadMachine.run (preservingReadGapFuel gap i)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapRawTape witness gap i rawTail }).state =
      .halt (witness.getD i false) := by
  rw [preservingReadGapRaw_forall i witness rawTail gap h]

#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingMovedGapRaw_forall
#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_forall
#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_forall_value


#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_zero
#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_start_successor

end P01WitnessIndexedReadGapRaw
end Real
end MCore
