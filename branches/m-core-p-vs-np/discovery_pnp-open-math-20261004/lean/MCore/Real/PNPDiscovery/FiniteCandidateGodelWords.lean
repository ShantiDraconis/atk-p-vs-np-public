import MCore.Real.PNPDiscovery.UnaryListSerialization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Flatten one transition row to three natural words. -/
def transitionRowWords
    {qCount : Nat}
    (r : TransitionRow qCount) : List Nat :=
  [r.nextState.val, r.writeSymbol.val, r.direction.val]

@[simp] theorem transitionRowWords_length
    {qCount : Nat}
    (r : TransitionRow qCount) :
    (transitionRowWords r).length = 3 := by
  rfl

/-- State-major, symbol-minor ordering of the finite transition table. -/
def transitionTableWords
    (D : FiniteCandidateDescription) : List Nat :=
  (List.ofFn fun q : Fin (D.stateCount + 1) =>
    (List.ofFn fun s : Fin 3 =>
      transitionRowWords (D.transitionTable q s)).flatten).flatten

def haltingTableWords
    (D : FiniteCandidateDescription) : List Nat :=
  (List.ofFn D.haltingTable).map boolWord

def acceptingTableWords
    (D : FiniteCandidateDescription) : List Nat :=
  (List.ofFn D.acceptingTable).map boolWord

/-- Complete finite word-level Gödel payload.
Header: stateCount, initial state, polynomial coefficient, exponent.
Then transition, halting and accepting tables. -/
def finiteDescriptionWords
    (D : FiniteCandidateDescription) : List Nat :=
  [D.stateCount,
   D.initial.val,
   D.clockCoefficient,
   D.clockExponent] ++
  transitionTableWords D ++
  haltingTableWords D ++
  acceptingTableWords D

theorem haltingTableWords_length
    (D : FiniteCandidateDescription) :
    (haltingTableWords D).length = D.stateCount + 1 := by
  simp [haltingTableWords]

theorem acceptingTableWords_length
    (D : FiniteCandidateDescription) :
    (acceptingTableWords D).length = D.stateCount + 1 := by
  simp [acceptingTableWords]

/-- Exact number of natural words in the transition table. -/
theorem transitionTableWords_length
    (D : FiniteCandidateDescription) :
    (transitionTableWords D).length =
      (D.stateCount + 1) * 3 * 3 := by
  unfold transitionTableWords
  simp [transitionRowWords]
  ring

/-- Exact total word count of a normalized candidate description. -/
theorem finiteDescriptionWords_length
    (D : FiniteCandidateDescription) :
    (finiteDescriptionWords D).length =
      4 + (D.stateCount + 1) * 9 +
        2 * (D.stateCount + 1) := by
  unfold finiteDescriptionWords
  rw [List.length_append, List.length_append, List.length_append]
  rw [transitionTableWords_length,
    haltingTableWords_length,
    acceptingTableWords_length]
  simp
  ring

/-- Concrete bitstring Gödel payload using the closed unary list codec. -/
def encodeFiniteDescription
    (D : FiniteCandidateDescription) : BitString :=
  encodeNatList (finiteDescriptionWords D)

theorem encodeFiniteDescription_length_exact
    (D : FiniteCandidateDescription) :
    (encodeFiniteDescription D).length =
      (finiteDescriptionWords D).length + 1 +
        ((finiteDescriptionWords D).map (fun n => n + 1)).sum := by
  exact encodeNatList_length (finiteDescriptionWords D)

/-- Decoding the outer unary serialization is already CLOSED. -/
theorem decodeFiniteDescriptionWords_roundTrip
    (D : FiniteCandidateDescription) :
    decodeNatList (encodeFiniteDescription D) =
      some (finiteDescriptionWords D, []) := by
  exact decodeNatList_encode D.finiteDescriptionWords

/-- The remaining codec obligation has been reduced to one finite table
reconstruction function over the decoded word vector. -/
structure FiniteTableReconstructor where
  reconstruct :
    List Nat → Option FiniteCandidateDescription
  exact :
    ∀ D : FiniteCandidateDescription,
      reconstruct (finiteDescriptionWords D) = some D

def FiniteTableReconstructorGap : Prop :=
  Nonempty FiniteTableReconstructor

/-- A table reconstructor immediately closes the earlier finite-description
codec gap; serialization contributes no further open mathematics. -/
def codecOfReconstructor
    (R : FiniteTableReconstructor) :
    FiniteDescriptionCodec where
  encode := encodeFiniteDescription
  decode := fun bits => do
    let (words, tail) ← decodeNatList bits
    if tail = [] then
      R.reconstruct words
    else
      none
  roundTrip := by
    intro D
    unfold encodeFiniteDescription
    rw [decodeNatList_encode]
    simp [R.exact D]

theorem reconstructor_closes_codec
    (H : FiniteTableReconstructorGap) :
    FiniteDescriptionCodecGap := by
  rcases H with ⟨R⟩
  exact ⟨codecOfReconstructor R⟩

/-- No mathematical endpoint content remains in the coding layer: the sole
open atom is finite dependent-table reconstruction. -/
def CurrentGodelCodingOpenAtom : Prop :=
  FiniteTableReconstructorGap

#print axioms MCore.Real.PNPDiscovery.transitionTableWords_length
#print axioms MCore.Real.PNPDiscovery.finiteDescriptionWords_length
#print axioms MCore.Real.PNPDiscovery.decodeFiniteDescriptionWords_roundTrip
#print axioms MCore.Real.PNPDiscovery.reconstructor_closes_codec

end PNPDiscovery
end Real
end MCore
