import MCore.Real.CanonicalSATNatParserAttack

namespace MCore
namespace Real
namespace CanonicalSATFrameAttack

open CanonicalFinalProof

/-- Recursive parser continuation frames needed by prefix Circuit parsing.
    Binary constructors need two phases: waiting for the left child and then
    waiting for the right child. -/
inductive Frame where
  | neg
  | andLeft
  | andRight
  | orLeft
  | orRight
  deriving DecidableEq, Repr

/-- Fixed-width binary representation of parser frames. -/
def encodeFrame : Frame → List Bool
  | .neg      => [false, false, false]
  | .andLeft  => [false, false, true]
  | .andRight => [false, true, false]
  | .orLeft   => [false, true, true]
  | .orRight  => [true, false, false]

def decodeFrame : List Bool → Option Frame
  | [false, false, false] => some .neg
  | [false, false, true]  => some .andLeft
  | [false, true, false]  => some .andRight
  | [false, true, true]   => some .orLeft
  | [true, false, false]  => some .orRight
  | _ => none

@[simp] theorem decodeFrame_encodeFrame
    (f : Frame) :
    decodeFrame (encodeFrame f) = some f := by
  cases f <;> rfl

@[simp] theorem encodeFrame_length
    (f : Frame) :
    (encodeFrame f).length = 3 := by
  cases f <;> rfl

def encodeFrames : List Frame → List Bool
  | [] => []
  | f :: fs => encodeFrame f ++ encodeFrames fs

def decodeFrames : List Bool → Option (List Frame)
  | [] => some []
  | a :: b :: c :: rest => do
      let f ← decodeFrame [a,b,c]
      let fs ← decodeFrames rest
      some (f :: fs)
  | _ => none

theorem decodeFrames_encodeFrames
    (fs : List Frame) :
    decodeFrames (encodeFrames fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f <;>
        simp [encodeFrames, encodeFrame, decodeFrames, decodeFrame, ih]

theorem encodeFrames_length
    (fs : List Frame) :
    (encodeFrames fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [encodeFrames, encodeFrame_length, ih]
      omega

theorem encoded_stack_linear_space
    (fs : List Frame)
    (inputLength : Nat)
    (hDepth : fs.length ≤ inputLength) :
    (encodeFrames fs).length ≤ 3 * inputLength := by
  rw [encodeFrames_length]
  exact Nat.mul_le_mul_left 3 hDepth

/-- Functional push representation; the machine-level implementation is still
    required separately. -/
theorem encodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    encodeFrames (f :: fs) =
      encodeFrame f ++ encodeFrames fs := by
  rfl

/-- Functional pop round-trip after decoding a well-formed encoded stack. -/
theorem decodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    decodeFrames (encodeFrame f ++ encodeFrames fs) =
      some (f :: fs) := by
  simpa [encodeFrames] using decodeFrames_encodeFrames (f :: fs)

/-!
Fail-proof hardening of the frame-tape boundary.

The previous certificate carried only an arbitrary machine and a polynomial
bound.  That shape is trivially inhabitable and therefore cannot certify
frame push/pop semantics.  The hardened certificate below fixes an explicit
command protocol and requires the machine to halt and return the exact
canonical stack encoding.
-/

def pushCommand (f : Frame) (fs : List Frame) : BitString :=
  true :: (encodeFrame f ++ encodeFrames fs)

def popCommand (fs : List Frame) : BitString :=
  false :: encodeFrames fs

/-- Legacy under-specified shape, retained only for the fail-proof theorem. -/
structure LegacyFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

/-- The legacy gate is vacuous: a one-state halted machine with zero time
    bound inhabits it without implementing any stack operation. -/
theorem legacy_frame_gate_is_trivially_inhabited :
    Nonempty LegacyFrameTapeMachineCertificate := by
  let trivialMachine : TM (Fin 1) (Option Bool) :=
    { initial := 0
      blank := none
      transition := fun q symbol => (q, symbol, .stay)
      halting := fun _ => true }
  have hpoly : PolynomialTimeBound (fun _ => 0) := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp
  exact ⟨
    { stateCount := 0
      machine := trivialMachine
      timeBound := fun _ => 0
      time_poly := hpoly }⟩

/-- Read the finite Boolean word from the current head to the first blank.
    Explicit blanks after the semantic end are ignored, matching the intended
    infinite-blank tape semantics rather than raw list representation. -/
def readTapeCells : List (Option Bool) → BitString
  | [] => []
  | none :: _ => []
  | some b :: rest => b :: readTapeCells rest

/-- Boolean word represented from the current tape head. -/
def tapeWord (t : Tape (Option Bool)) : BitString :=
  match t.head with
  | none => []
  | some b => b :: readTapeCells t.right

/-- Canonical-head semantic representation: the machine has rewound to the
    left boundary and the visible word agrees with the requested bitstring. -/
def TapeRepresents (bits : BitString) (t : Tape (Option Bool)) : Prop :=
  t.left = [] ∧ tapeWord t = bits

@[simp] theorem readTapeCells_map_some
    (bits : BitString) :
    readTapeCells (bits.map some) = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      simp [readTapeCells, ih]

@[simp] theorem tapeWord_inputTape
    (bits : BitString) :
    tapeWord (inputTape bits) = bits := by
  cases bits <;> simp [tapeWord, inputTape, readTapeCells]

theorem inputTape_represents
    (bits : BitString) :
    TapeRepresents bits (inputTape bits) := by
  constructor
  · cases bits <;> rfl
  · exact tapeWord_inputTape bits

/-- Raw Tape equality is strictly stronger than represented-word equality:
    an explicit trailing blank changes the structure but not the word. -/
def trailingBlankTape : Tape (Option Bool) :=
  { left := [], head := some true, right := [none] }

theorem trailingBlankTape_represents :
    TapeRepresents [true] trailingBlankTape := by
  simp [TapeRepresents, trailingBlankTape, tapeWord, readTapeCells]

theorem trailingBlankTape_ne_inputTape :
    trailingBlankTape ≠ inputTape [true] := by
  simp [trailingBlankTape, inputTape]

/-- Hardened operational boundary.  Push is presented as
    1 || frame || stack and pop as 0 || stack.  Successful execution must
    normalize the final tape back to the canonical stack encoding. -/
structure FrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))

  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      (machine.run
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))).tape =
      inputTape (encodeFrames (f :: fs))

  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))

  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      (machine.run
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))).tape =
      inputTape (encodeFrames fs)

def FrameTapeOperationalGap : Prop :=
  Nonempty FrameTapeMachineCertificate

/-- Semantically hardened variant: exact represented output is required, while
    harmless explicit trailing blanks are quotient-like implementation detail. -/
structure SemanticFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))

  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresents
        (encodeFrames (f :: fs))
        (machine.run
          (timeBound (pushCommand f fs).length)
          (initialTMConfig machine (pushCommand f fs))).tape

  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))

  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresents
        (encodeFrames fs)
        (machine.run
          (timeBound (popCommand (f :: fs)).length)
          (initialTMConfig machine (popCommand (f :: fs)))).tape

def SemanticFrameTapeOperationalGap : Prop :=
  Nonempty SemanticFrameTapeMachineCertificate

def FrameTapeMachineCertificate.toSemantic
    (C : FrameTapeMachineCertificate) :
    SemanticFrameTapeMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly
    push_halts := C.push_halts
    push_correct := by
      intro f fs
      rw [C.push_correct f fs]
      exact inputTape_represents _
    pop_halts := C.pop_halts
    pop_correct := by
      intro f fs
      rw [C.pop_correct f fs]
      exact inputTape_represents _ }

theorem exact_frame_tape_implies_semantic
    (h : FrameTapeOperationalGap) :
    SemanticFrameTapeOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toSemantic⟩

#print axioms MCore.Real.CanonicalSATFrameAttack.trailingBlankTape_ne_inputTape
#print axioms MCore.Real.CanonicalSATFrameAttack.exact_frame_tape_implies_semantic

/-- The hardened frame-tape certificate is strong enough to discharge the
    earlier structural recursive-frame existence gate.  This does not create
    the missing machine; it wires a genuine future implementation into the
    existing parser chain without weakening its semantics. -/
def FrameTapeMachineCertificate.toRecursiveFrameMachineCertificate
    (C : FrameTapeMachineCertificate) :
    CanonicalSATNatParserAttack.RecursiveFrameMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem frame_tape_operational_closes_recursive_frame
    (h : FrameTapeOperationalGap) :
    CanonicalSATNatParserAttack.RecursiveFrameOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toRecursiveFrameMachineCertificate⟩

#print axioms MCore.Real.CanonicalSATFrameAttack.frame_tape_operational_closes_recursive_frame

#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrame_encodeFrame
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_encodeFrames
#print axioms MCore.Real.CanonicalSATFrameAttack.encodeFrames_length
#print axioms MCore.Real.CanonicalSATFrameAttack.encoded_stack_linear_space
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_push
#print axioms MCore.Real.CanonicalSATFrameAttack.legacy_frame_gate_is_trivially_inhabited

end CanonicalSATFrameAttack
end Real
end MCore
