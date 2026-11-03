import MCore.Real.PNPDiscovery.OrbitArithmetic

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence

/-- Terminal control state reached by the deterministic candidate at its
declared polynomial clock.  This is strictly below the Boolean acceptance
observable and contains no P/NP endpoint vocabulary. -/
def terminalState
    (M : PolyDTMCandidate)
    (x : BitString) :
    Fin (M.stateCount + 1) :=
  (M.machine.run
    (M.timeBound x.length)
    (initialTMConfig M.machine x)).state

theorem declaredAccepts_iff_terminalState
    (M : PolyDTMCandidate)
    (x : BitString) :
    DeclaredAccepts M x ↔
      M.accepting (terminalState M x) = true := by
  rfl

/-- A genuinely structural odd recurrence asks for equality of terminal
machine states, not merely equality of their accepting labels. -/
def OddTerminalStateRecurrence
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∃ seed : BitString, ∃ i d : Nat,
    terminalState M
        (orbit M hTotal seed (i + (2 * d + 1))) =
      terminalState M (orbit M hTotal seed i)

/-- Equality of terminal states transports immediately to equality of the
declared acceptance observable. -/
theorem oddTerminalStateRecurrence_to_observable
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : OddTerminalStateRecurrence M hTotal) :
    ∃ seed : BitString, ∃ i d : Nat,
      DeclaredAccepts M
          (orbit M hTotal seed (i + (2 * d + 1))) ↔
        DeclaredAccepts M (orbit M hTotal seed i) := by
  rcases H with ⟨seed, i, d, hState⟩
  refine ⟨seed, i, d, ?_⟩
  unfold DeclaredAccepts terminalState at *
  rw [hState]

/-- Uniform structural producer.  Unlike ObservableRecurrenceProducer this is
not definitionally or logically identified with the exact frontier by the
current library: it demands a concrete state collision across odd parity. -/
def TerminalStateRecurrenceProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    OddTerminalStateRecurrence M hTotal

theorem terminalStateRecurrence_to_observable
    (B : TerminalStateRecurrenceProducer) :
    ObservableRecurrenceProducer := by
  intro M hTotal
  exact oddTerminalStateRecurrence_to_observable
    M hTotal (B M hTotal)

theorem terminalStateRecurrence_to_exact
    (B : TerminalStateRecurrenceProducer) :
    TotalExactDiagonalProducer :=
  observableRecurrence_closes_exact_frontier
    (terminalStateRecurrence_to_observable B)

/-- Exact opposite structural regime for one candidate.  If the new producer
fails, every odd-separated pair on every concrete reduction orbit must end in
different terminal control states. -/
def TerminalParityBarrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ seed : BitString, ∀ i d : Nat,
    terminalState M
        (orbit M hTotal seed (i + (2 * d + 1))) ≠
      terminalState M (orbit M hTotal seed i)

theorem terminalRecurrence_or_parityBarrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    OddTerminalStateRecurrence M hTotal ∨
      TerminalParityBarrier M hTotal := by
  classical
  by_cases h : OddTerminalStateRecurrence M hTotal
  · exact Or.inl h
  · right
    intro seed i d hEq
    apply h
    exact ⟨seed, i, d, hEq⟩

/-- A terminal parity barrier is strong enough to exclude every odd terminal
state recurrence but, by itself, says nothing about whether the accepting
labels differ.  This is the next structural branch to attack. -/
theorem parityBarrier_no_terminalRecurrence
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (H : TerminalParityBarrier M hTotal) :
    ¬ OddTerminalStateRecurrence M hTotal := by
  rintro ⟨seed, i, d, hEq⟩
  exact H seed i d hEq

#print axioms MCore.Real.PNPDiscovery.declaredAccepts_iff_terminalState
#print axioms MCore.Real.PNPDiscovery.oddTerminalStateRecurrence_to_observable
#print axioms MCore.Real.PNPDiscovery.terminalStateRecurrence_to_observable
#print axioms MCore.Real.PNPDiscovery.terminalStateRecurrence_to_exact
#print axioms MCore.Real.PNPDiscovery.terminalRecurrence_or_parityBarrier
#print axioms MCore.Real.PNPDiscovery.parityBarrier_no_terminalRecurrence

end PNPDiscovery
end Real
end MCore
