import MCore.Real.PNPDiscovery.CanonicalClockNormalization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Finite symbol alphabet of the hardened candidate model. -/
def symbolCode : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def symbolOfCode : Fin 3 → Option Bool
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => some false
  | _ => some true

theorem symbolOfCode_symbolCode
    (s : Option Bool) :
    symbolOfCode (symbolCode s) = s := by
  cases s with
  | none => rfl
  | some b =>
      cases b <;> rfl

def directionCode : Direction → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

def directionOfCode : Fin 3 → Direction
  | ⟨0, _⟩ => .left
  | ⟨1, _⟩ => .stay
  | _ => .right

theorem directionOfCode_directionCode
    (d : Direction) :
    directionOfCode (directionCode d) = d := by
  cases d <;> rfl

/-- One finite transition-table row. -/
structure TransitionRow (qCount : Nat) where
  nextState : Fin (qCount + 1)
  writeSymbol : Fin 3
  direction : Fin 3
  deriving DecidableEq

/-- Fully finite operational description of a normalized candidate. -/
structure FiniteCandidateDescription where
  stateCount : Nat
  initial : Fin (stateCount + 1)
  transitionTable :
    Fin (stateCount + 1) → Fin 3 →
      TransitionRow stateCount
  haltingTable : Fin (stateCount + 1) → Bool
  acceptingTable : Fin (stateCount + 1) → Bool
  clockCoefficient : Nat
  clockExponent : Nat

/-- Reconstruct the actual TM from the finite description. -/
def FiniteCandidateDescription.machine
    (D : FiniteCandidateDescription) :
    TM (Fin (D.stateCount + 1)) (Option Bool) :=
  { initial := D.initial
    blank := none
    transition := fun q s =>
      let row := D.transitionTable q (symbolCode s)
      (row.nextState,
        symbolOfCode row.writeSymbol,
        directionOfCode row.direction)
    halting := D.haltingTable }

/-- Reconstruct its canonical polynomial clock. -/
def FiniteCandidateDescription.clock
    (D : FiniteCandidateDescription) :
    TimeBound :=
  fun n =>
    D.clockCoefficient * (n + 1) ^ D.clockExponent

theorem finiteDescription_clock_poly
    (D : FiniteCandidateDescription) :
    PolynomialTimeBound D.clock := by
  exact ⟨D.clockCoefficient, D.clockExponent, fun _ => le_rfl⟩

def FiniteCandidateDescription.toCandidate
    (D : FiniteCandidateDescription) :
    PolyDTMCandidate :=
  { stateCount := D.stateCount
    machine := D.machine
    blank_none := rfl
    accepting := D.acceptingTable
    timeBound := D.clock
    time_poly := finiteDescription_clock_poly D }

/-- Extract a finite description from the canonical-clock normalization of a
candidate. -/
noncomputable def finiteDescription
    (M : PolyDTMCandidate) :
    FiniteCandidateDescription :=
  { stateCount := M.stateCount
    initial := M.machine.initial
    transitionTable := fun q s =>
      let out := M.machine.transition q (symbolOfCode s)
      { nextState := out.1
        writeSymbol := symbolCode out.2.1
        direction := directionCode out.2.2 }
    haltingTable := M.machine.halting
    acceptingTable := M.accepting
    clockCoefficient := (clockEnvelope M).coefficient
    clockExponent := (clockEnvelope M).exponent }

/-- Transition reconstruction is exact on the hardened alphabet. -/
theorem finiteDescription_transition_roundTrip
    (M : PolyDTMCandidate)
    (q : Fin (M.stateCount + 1))
    (s : Option Bool) :
    (finiteDescription M).machine.transition q s =
      M.machine.transition q s := by
  unfold finiteDescription FiniteCandidateDescription.machine
  simp [symbolOfCode_symbolCode]
  rcases h :
      M.machine.transition q s with
    ⟨q', w, d⟩
  simp [h, symbolOfCode_symbolCode,
    directionOfCode_directionCode]

theorem finiteDescription_halting_roundTrip
    (M : PolyDTMCandidate) :
    (finiteDescription M).machine.halting =
      M.machine.halting := by
  rfl

theorem finiteDescription_initial_roundTrip
    (M : PolyDTMCandidate) :
    (finiteDescription M).machine.initial =
      M.machine.initial := by
  rfl

theorem finiteDescription_accepting_roundTrip
    (M : PolyDTMCandidate) :
    (finiteDescription M).acceptingTable = M.accepting := by
  rfl

theorem finiteDescription_clock_eq
    (M : PolyDTMCandidate) :
    (finiteDescription M).clock = canonicalClock M := by
  rfl

/-- Exact semantic target for the finite-description layer. -/
def FiniteDescriptionSemanticRoundTrip : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (x : BitString),
    DeclaredAccepts ((finiteDescription M).toCandidate) x ↔
      DeclaredAccepts M x

theorem finiteDescription_semantic_roundTrip_closed :
    FiniteDescriptionSemanticRoundTrip := by
  intro M hTotal x
  have hCanon :=
    canonicalClock_declaredAccepts_iff M hTotal x
  change
    DeclaredAccepts (canonicalClockCandidate M) x ↔
      DeclaredAccepts M x
  exact hCanon

/-- What remains for Gödel coding is now only finite serialization. -/
structure FiniteDescriptionCodec where
  encode : FiniteCandidateDescription → BitString
  decode : BitString → Option FiniteCandidateDescription
  roundTrip :
    ∀ D : FiniteCandidateDescription,
      decode (encode D) = some D

def FiniteDescriptionCodecGap : Prop :=
  Nonempty FiniteDescriptionCodec

#print axioms MCore.Real.PNPDiscovery.finiteDescription_transition_roundTrip
#print axioms MCore.Real.PNPDiscovery.finiteDescription_semantic_roundTrip_closed

end PNPDiscovery
end Real
end MCore
