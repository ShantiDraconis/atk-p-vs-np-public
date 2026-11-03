import MCore.Real.PNPDiscovery.ReadCone

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction

/-- A purely input-structural odd collision: two odd-separated orbit points
have equal length and agree on the full read cone of the earlier point. -/
def OddReadConeCollision
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∃ seed : BitString, ∃ i d : Nat,
    let x := orbit M hTotal seed i
    let y := orbit M hTotal seed (i + (2 * d + 1))
    x.length = y.length ∧
      x.take (ReadConePrefix M x) =
        y.take (ReadConePrefix M x)

/-- A read-cone collision forces equality of terminal states. -/
theorem oddReadConeCollision_to_terminal
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : OddReadConeCollision M hTotal) :
    OddTerminalStateRecurrence M hTotal := by
  rcases H with ⟨seed, i, d, hLen, hCone⟩
  refine ⟨seed, i, d, ?_⟩
  exact (readCone_invisibility
    M
    (orbit M hTotal seed (i + (2 * d + 1)))
    (orbit M hTotal seed i)
    hLen.symm
    ?_)
  have hT :
      ReadConePrefix M
          (orbit M hTotal seed (i + (2 * d + 1))) =
        ReadConePrefix M (orbit M hTotal seed i) := by
    unfold ReadConePrefix
    rw [hLen]
  rw [hT]
  exact hCone.symm

/-- Uniform structural producer below the terminal-state frontier. -/
def ReadConeCollisionProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    OddReadConeCollision M hTotal

theorem readConeCollision_to_terminalProducer
    (B : ReadConeCollisionProducer) :
    TerminalStateRecurrenceProducer := by
  intro M hTotal
  exact oddReadConeCollision_to_terminal M hTotal (B M hTotal)

theorem readConeCollision_to_exact
    (B : ReadConeCollisionProducer) :
    TotalExactDiagonalProducer :=
  terminalStateRecurrence_to_exact
    (readConeCollision_to_terminalProducer B)

/-- Exact concrete obstruction induced by a terminal parity barrier:
every odd-separated pair must either have different length, or differ inside
the bounded prefix that the earlier run can inspect. -/
theorem parityBarrier_forces_length_or_prefix_difference
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed i
    let y := orbit M hTotal seed (i + (2 * d + 1))
    x.length ≠ y.length ∨
      x.take (ReadConePrefix M x) ≠
        y.take (ReadConePrefix M x) := by
  dsimp
  classical
  by_cases hLen :
      (orbit M hTotal seed i).length =
        (orbit M hTotal seed (i + (2 * d + 1))).length
  · right
    intro hPrefix
    have hState :
        terminalState M (orbit M hTotal seed i) =
          terminalState M
            (orbit M hTotal seed (i + (2 * d + 1))) :=
      readCone_invisibility
        M
        (orbit M hTotal seed i)
        (orbit M hTotal seed (i + (2 * d + 1)))
        hLen
        hPrefix
    exact H seed i d hState.symm
  · exact Or.inl hLen

/-- The next open structural target is now explicit: manufacture one odd pair
for which both length and the entire observable prefix coincide. -/
def ReadConePairProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ∃ seed : BitString, ∃ i d : Nat,
      let x := orbit M hTotal seed i
      let y := orbit M hTotal seed (i + (2 * d + 1))
      x.length = y.length ∧
        x.take (ReadConePrefix M x) =
          y.take (ReadConePrefix M x)

theorem readConePairProducer_to_collision
    (B : ReadConePairProducer) :
    OrbitCollisionProducer :=
  observableRecurrence_to_collision
    (terminalStateRecurrence_to_observable
      (readConeCollision_to_terminalProducer B))

#print axioms MCore.Real.PNPDiscovery.oddReadConeCollision_to_terminal
#print axioms MCore.Real.PNPDiscovery.readConeCollision_to_terminalProducer
#print axioms MCore.Real.PNPDiscovery.readConeCollision_to_exact
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_length_or_prefix_difference
#print axioms MCore.Real.PNPDiscovery.readConePairProducer_to_collision


/-- Corrected structural frontier: total length equality is unnecessary.
Two odd-separated orbit points only need to agree on the prefix visible before
the smaller of their two declared clocks. -/
def OddSharedReadConeCollision
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∃ seed : BitString, ∃ i d : Nat,
    let x := orbit M hTotal seed i
    let y := orbit M hTotal seed (i + (2 * d + 1))
    x.take (SharedReadConePrefix M x y) =
      y.take (SharedReadConePrefix M x y)

theorem oddSharedReadConeCollision_to_terminal
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : OddSharedReadConeCollision M hTotal) :
    OddTerminalStateRecurrence M hTotal := by
  rcases H with ⟨seed, i, d, hCone⟩
  refine ⟨seed, i, d, ?_⟩
  exact (sharedReadCone_invisibility
    M hTotal
    (orbit M hTotal seed (i + (2 * d + 1)))
    (orbit M hTotal seed i)
    ?_)
  unfold SharedReadConePrefix at *
  rw [Nat.min_comm]
  exact hCone.symm

def SharedReadConeCollisionProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    OddSharedReadConeCollision M hTotal

theorem sharedReadConeCollision_to_exact
    (B : SharedReadConeCollisionProducer) :
    TotalExactDiagonalProducer := by
  apply terminalStateRecurrence_to_exact
  intro M hTotal
  exact oddSharedReadConeCollision_to_terminal
    M hTotal (B M hTotal)

/-- If terminal recurrence is impossible, then every odd pair must differ
inside the genuinely observable shared cone.  No global length alternative
remains. -/
theorem parityBarrier_forces_sharedCone_difference
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed i
    let y := orbit M hTotal seed (i + (2 * d + 1))
    x.take (SharedReadConePrefix M x y) ≠
      y.take (SharedReadConePrefix M x y) := by
  dsimp
  intro hCone
  have hState :=
    sharedReadCone_invisibility
      M hTotal
      (orbit M hTotal seed i)
      (orbit M hTotal seed (i + (2 * d + 1)))
      hCone
  exact H seed i d hState.symm

#print axioms MCore.Real.PNPDiscovery.oddSharedReadConeCollision_to_terminal
#print axioms MCore.Real.PNPDiscovery.sharedReadConeCollision_to_exact
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_sharedCone_difference

end PNPDiscovery
end Real
end MCore
