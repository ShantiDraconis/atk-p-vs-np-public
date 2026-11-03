import MCore.Real.P02UniversalFailureWitnessMaterial

namespace MCore
namespace Real
namespace P02TerminalForcingG2

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial

abbrev CanonicalSAT : BitLanguage :=
  P02UniversalFailureWitnessMaterial.CanonicalSAT

/-- A concrete selector M ↦ x_M. -/
abbrev CounterexampleSelector :=
  PolyDTMCandidate → BitString

/-- Fully expanded law that the selected x_M must satisfy. -/
def FailureLaw (xM : CounterexampleSelector) : Prop :=
  ∀ M : PolyDTMCandidate,
    ¬ (
      M.machine.HaltsWithin
        (M.timeBound (xM M).length)
        (initialTMConfig M.machine (xM M)) ∧
      (M.accepting
          (M.machine.run
            (M.timeBound (xM M).length)
            (initialTMConfig M.machine (xM M))).state = true ↔
        CanonicalSAT (xM M))
    )

theorem failureLaw_iff_correctAt
    (xM : CounterexampleSelector) :
    FailureLaw xM ↔
      ∀ M : PolyDTMCandidate,
        ¬ M.CorrectAt CanonicalSAT (xM M) := by
  rfl

/-- Requested terminal constructor: an actual x_M plus the universal failure law
constructs the exact UniversalFailureWitness. -/
def universalFailureWitnessOf
    (xM : CounterexampleSelector)
    (h : FailureLaw xM) :
    UniversalFailureWitness :=
  { counterexample := xM
    fails := by
      intro M
      exact (failureLaw_iff_correctAt xM).mp h M }

/-- Exact terminal G2 obligation with selector and proof exposed separately. -/
def G2_TERMINAL : Prop :=
  ∃ xM : CounterexampleSelector, FailureLaw xM

theorem g2_terminal_iff_witness :
    G2_TERMINAL ↔ Nonempty UniversalFailureWitness := by
  constructor
  · rintro ⟨xM, h⟩
    exact ⟨universalFailureWitnessOf xM h⟩
  · rintro ⟨W⟩
    exact ⟨W.counterexample, (failureLaw_iff_correctAt W.counterexample).mpr W.fails⟩

theorem g2_terminal_implies_p_ne_np
    (h : G2_TERMINAL) :
    PneqNP := by
  rcases h with ⟨xM, hx⟩
  exact witness_implies_p_ne_np (universalFailureWitnessOf xM hx)

#print axioms MCore.Real.P02TerminalForcingG2.failureLaw_iff_correctAt
#print axioms MCore.Real.P02TerminalForcingG2.universalFailureWitnessOf
#print axioms MCore.Real.P02TerminalForcingG2.g2_terminal_iff_witness
#print axioms MCore.Real.P02TerminalForcingG2.g2_terminal_implies_p_ne_np

end P02TerminalForcingG2
end Real
end MCore
