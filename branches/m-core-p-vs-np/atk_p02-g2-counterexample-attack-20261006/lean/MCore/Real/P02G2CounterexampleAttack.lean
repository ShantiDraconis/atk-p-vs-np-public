import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02G2CounterexampleAttack

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

/--
Canonical material frontier for G2.

The selector field is easy to inhabit as a bare function type. The mathematical
content is the coupled universal failure law for the chosen selector.
-/
def COUNTEREXAMPLE_MATERIAL_OPEN_MATH : Prop :=
  ∃ counterexample : PolyDTMCandidate → BitString,
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt
        P02TerminalForcingG2.CanonicalSAT
        (counterexample M)

/-- Bare selector inhabitation is structural only; it does not close any G2 payload. -/
def trivialSelector : CounterexampleSelector :=
  fun _ => []

theorem counterexampleSelector_nonempty :
    Nonempty CounterexampleSelector :=
  ⟨trivialSelector⟩

/-- Failure obligation for one explicitly supplied selector. -/
def SelectorFails (xM : CounterexampleSelector) : Prop :=
  ∀ M : PolyDTMCandidate,
    ¬ M.CorrectAt
      P02TerminalForcingG2.CanonicalSAT
      (xM M)

theorem selectorFails_iff_failureLaw
    (xM : CounterexampleSelector) :
    SelectorFails xM ↔ FailureLaw xM := by
  rfl


/-- Concrete timeout branch of failure at one input. -/
def DeclaredTimeout
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  ¬ M.machine.HaltsWithin
      (M.timeBound x.length)
      (initialTMConfig M.machine x)

/-- Concrete semantic-disagreement branch, evaluated at the declared clock. -/
def SemanticMismatch
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  ¬ (
    M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = true ↔
      P02TerminalForcingG2.CanonicalSAT x)

/-- Exact local split of candidate failure into timeout or semantic mismatch. -/
theorem not_correctAt_iff_timeout_or_mismatch
    (M : PolyDTMCandidate)
    (x : BitString) :
    ¬ M.CorrectAt P02TerminalForcingG2.CanonicalSAT x ↔
      DeclaredTimeout M x ∨ SemanticMismatch M x := by
  constructor
  · intro h
    by_cases hhalt :
        M.machine.HaltsWithin
          (M.timeBound x.length)
          (initialTMConfig M.machine x)
    · right
      intro hsem
      exact h ⟨hhalt, hsem⟩
    · left
      exact hhalt
  · intro h hcorrect
    rcases h with htimeout | hmismatch
    · exact htimeout hcorrect.1
    · exact hmismatch hcorrect.2

/-- Pointwise formulation: each candidate has some concrete failing input. -/
def POINTWISE_FAILURE_OPEN_MATH : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      DeclaredTimeout M x ∨ SemanticMismatch M x

/--
Classical choice only packages already-existing pointwise witnesses into one
selector. It contributes no lower-bound mathematics.
-/
theorem pointwiseFailure_iff_counterexampleMaterial :
    POINTWISE_FAILURE_OPEN_MATH ↔ COUNTEREXAMPLE_MATERIAL_OPEN_MATH := by
  constructor
  · intro h
    classical
    let pick : PolyDTMCandidate → BitString :=
      fun M => Classical.choose (h M)
    refine ⟨pick, ?_⟩
    intro M
    exact (not_correctAt_iff_timeout_or_mismatch M (pick M)).2
      (Classical.choose_spec (h M))
  · rintro ⟨pick, hFail⟩
    intro M
    exact ⟨pick M,
      (not_correctAt_iff_timeout_or_mismatch M (pick M)).1 (hFail M)⟩

/--
Exact exposure audit: the coupled selector+failure frontier is definitionally
the same obligation as G2_TERMINAL. This theorem is an A-route equivalence only;
it is not a producer.
-/
theorem counterexampleMaterial_iff_terminal :
    COUNTEREXAMPLE_MATERIAL_OPEN_MATH ↔
      P02TerminalForcingG2.G2_TERMINAL := by
  rfl

/--
If the coupled terminal payload is ever materialized independently, it packages
into the already-audited UniversalFailureWitness constructor.
-/
def witnessOfCounterexampleMaterial
    (counterexample : PolyDTMCandidate → BitString)
    (fails : SelectorFails counterexample) :
    UniversalFailureWitness :=
  P02TerminalForcingG2.universalFailureWitnessOf counterexample fails


/-! ### T7 terminal-cycle compression

These names are deliberately definitionally identical.  The purpose of this
block is to prevent reopening the same terminal obligation under fresh labels.
-/

abbrev Endpoint : Prop := COUNTEREXAMPLE_MATERIAL_OPEN_MATH
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem endpoint_iff_gap : Endpoint ↔ Gap := Iff.rfl
theorem gap_iff_habitant : Gap ↔ Habitant := Iff.rfl
theorem habitant_iff_inhabitant : Habitant ↔ Inhabitant := Iff.rfl
theorem terminal_cycle : Endpoint ↔ Inhabitant := Iff.rfl

/-- The compressed endpoint is exactly the already-audited G2 terminal. -/
theorem endpoint_iff_g2_terminal :
    Endpoint ↔ P02TerminalForcingG2.G2_TERMINAL :=
  counterexampleMaterial_iff_terminal

/-- The compressed endpoint is exactly nonemptiness of the material universal
failure witness. -/
theorem endpoint_iff_universal_failure_witness :
    Endpoint ↔ Nonempty UniversalFailureWitness := by
  rw [endpoint_iff_g2_terminal]
  exact P02TerminalForcingG2.g2_terminal_iff_witness

/-- No extra proof obligation is introduced by the terminal names: inhabiting
any one of them is exactly inhabiting the material endpoint. -/
theorem inhabitant_iff_material_endpoint :
    Inhabitant ↔ COUNTEREXAMPLE_MATERIAL_OPEN_MATH := Iff.rfl

#print axioms MCore.Real.P02G2CounterexampleAttack.not_correctAt_iff_timeout_or_mismatch
#print axioms MCore.Real.P02G2CounterexampleAttack.pointwiseFailure_iff_counterexampleMaterial
#print axioms MCore.Real.P02G2CounterexampleAttack.counterexampleSelector_nonempty
#print axioms MCore.Real.P02G2CounterexampleAttack.selectorFails_iff_failureLaw
#print axioms MCore.Real.P02G2CounterexampleAttack.counterexampleMaterial_iff_terminal
#print axioms MCore.Real.P02G2CounterexampleAttack.witnessOfCounterexampleMaterial

end P02G2CounterexampleAttack
end Real
end MCore
