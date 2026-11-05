import MCore.Real.P02G21G22Attack
import MCore.Real.P02DiagonalFrontier

namespace MCore
namespace Research
namespace Prime2

open Real
open Real.CanonicalFinalProof
open Real.P02G21G22Attack
open Real.P02DiagonalFrontier

/-!
Prime2 conservative research model.

The experimental nucleus is metadata only.  The standard computational
vocabulary is evaluated exclusively on the raw standard candidate/input.
Consequently, no distinction between hypothetical nucleus tags can create a
new SAT, machine-execution, clock, polynomial-time, or CorrectAt fact.
-/

/-- Experimental nucleus metadata.  More than one tag may be represented at
the research level, but tags have no computational semantics in this file. -/
structure Nucleus where
  shell : Nat
  denominator : Nat
  deriving DecidableEq, Repr, BEq

/-- A Prime2 input is a standard bitstring plus experimental metadata. -/
structure Prime2BitString where
  raw : BitString
  nucleusTag : Option Nucleus
  deriving Repr

/-- A Prime2 candidate contains an actual standard candidate.  Experimental
metadata is deliberately absent from the standard machine semantics. -/
structure Prime2Candidate where
  raw : PolyDTMCandidate

/-- Canonical research embedding: standard inputs carry no experimental tag. -/
def mapInputStd (x : BitString) : Prime2BitString :=
  { raw := x, nucleusTag := none }

/-- Canonical candidate embedding preserves the machine literally. -/
def mapCandidateStd (M : PolyDTMCandidate) : Prime2Candidate :=
  { raw := M }

/-- A lightweight observational encoding used only to state literal preservation
of machine/input identity.  It is not claimed to be a canonical Gödel code. -/
def StdObservationEncode
    (M : PolyDTMCandidate) (x : BitString) :
    Nat × BitString :=
  (M.stateCount, x)

def Prime2ObservationEncode
    (M : Prime2Candidate) (x : Prime2BitString) :
    Nat × BitString :=
  (M.raw.stateCount, x.raw)

/-- Acceptance at the candidate's declared clock. -/
def Prime2Accepts
    (M : Prime2Candidate) (x : Prime2BitString) : Prop :=
  AcceptsAtDeclaredBound M.raw x.raw

/-- Halting at an arbitrary finite clock. -/
def StdHaltsInSteps
    (M : PolyDTMCandidate) (x : BitString) (k : Nat) : Prop :=
  M.machine.HaltsWithin k (initialTMConfig M.machine x)

def Prime2HaltsInSteps
    (M : Prime2Candidate) (x : Prime2BitString) (k : Nat) : Prop :=
  StdHaltsInSteps M.raw x.raw k

/-- Polynomiality is the real repository predicate on the declared time bound. -/
def StdPolyTime (M : PolyDTMCandidate) : Prop :=
  PolynomialTimeBound M.timeBound

def Prime2PolyTime (M : Prime2Candidate) : Prop :=
  StdPolyTime M.raw

/-- Prime2 SAT semantics ignore the experimental tag and read the raw bitstring. -/
def Prime2SAT (x : Prime2BitString) : Prop :=
  SATTarget x.raw

/-- Prime2 CorrectAt is exactly standard CorrectAt on raw objects. -/
def Prime2CorrectAt
    (M : Prime2Candidate) (x : Prime2BitString) : Prop :=
  M.raw.CorrectAt SATTarget x.raw

abbrev CorrectAtStd
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  M.CorrectAt SATTarget x

/-- Full conservative signature.  Each field states preservation in the exact
standard vocabulary available in this repository. -/
structure ConservativePrime2Interpretation where
  mapCandidate : PolyDTMCandidate → Prime2Candidate
  mapInput : BitString → Prime2BitString

  encode_eq :
    ∀ M x,
      Prime2ObservationEncode (mapCandidate M) (mapInput x) =
        StdObservationEncode M x

  input_same :
    ∀ x, (mapInput x).raw = x

  execution_preserved :
    ∀ M x,
      Prime2Accepts (mapCandidate M) (mapInput x) ↔
        AcceptsAtDeclaredBound M x

  clock_preserved :
    ∀ M x k,
      Prime2HaltsInSteps (mapCandidate M) (mapInput x) k ↔
        StdHaltsInSteps M x k

  poly_preserved :
    ∀ M,
      Prime2PolyTime (mapCandidate M) ↔ StdPolyTime M

  sat_preserved :
    ∀ x,
      Prime2SAT (mapInput x) ↔ SATTarget x

  correct_iff :
    ∀ M x,
      Prime2CorrectAt (mapCandidate M) (mapInput x) ↔
        CorrectAtStd M x

/-- The canonical raw embedding is conservative by reflexivity. -/
def canonicalInterpretation : ConservativePrime2Interpretation where
  mapCandidate := mapCandidateStd
  mapInput := mapInputStd
  encode_eq := by intro M x; rfl
  input_same := by intro x; rfl
  execution_preserved := by intro M x; rfl
  clock_preserved := by intro M x k; rfl
  poly_preserved := by intro M; rfl
  sat_preserved := by intro x; rfl
  correct_iff := by intro M x; rfl

def ConservativeInterpretationGap : Prop :=
  Nonempty ConservativePrime2Interpretation

theorem canonical_interpretation_exists :
    ConservativeInterpretationGap :=
  ⟨canonicalInterpretation⟩

/-- Lemma A: pointwise failure transfers directly through CorrectAt
conservativity. -/
theorem prime2_failure_transfers
    (I : ConservativePrime2Interpretation)
    (M : PolyDTMCandidate)
    (x : BitString)
    (h :
      ¬ Prime2CorrectAt (I.mapCandidate M) (I.mapInput x)) :
    ¬ CorrectAtStd M x := by
  intro hStd
  exact h ((I.correct_iff M x).mpr hStd)

/-- Restricted standard vocabulary used for the strong conservativity theorem.
It deliberately contains no nucleus predicates. -/
inductive StdFormula where
  | accepts
  | halts (k : Nat)
  | poly
  | sat
  | correct
  | neg (φ : StdFormula)
  | and (φ ψ : StdFormula)
  | or (φ ψ : StdFormula)
  deriving Repr

def evalStd
    (φ : StdFormula)
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  match φ with
  | .accepts => AcceptsAtDeclaredBound M x
  | .halts k => StdHaltsInSteps M x k
  | .poly => StdPolyTime M
  | .sat => SATTarget x
  | .correct => CorrectAtStd M x
  | .neg φ => ¬ evalStd φ M x
  | .and φ ψ => evalStd φ M x ∧ evalStd ψ M x
  | .or φ ψ => evalStd φ M x ∨ evalStd ψ M x

def evalPrime2
    (φ : StdFormula)
    (M : Prime2Candidate)
    (x : Prime2BitString) : Prop :=
  match φ with
  | .accepts => Prime2Accepts M x
  | .halts k => Prime2HaltsInSteps M x k
  | .poly => Prime2PolyTime M
  | .sat => Prime2SAT x
  | .correct => Prime2CorrectAt M x
  | .neg φ => ¬ evalPrime2 φ M x
  | .and φ ψ => evalPrime2 φ M x ∧ evalPrime2 ψ M x
  | .or φ ψ => evalPrime2 φ M x ∨ evalPrime2 ψ M x

/-- Lemma B: strong conservativity over the explicit standard vocabulary.
Nucleus tags are syntactically unavailable in StdFormula. -/
theorem conservative_over_std_vocab
    (I : ConservativePrime2Interpretation)
    (φ : StdFormula)
    (M : PolyDTMCandidate)
    (x : BitString) :
    evalPrime2 φ (I.mapCandidate M) (I.mapInput x) ↔
      evalStd φ M x := by
  induction φ with
  | accepts =>
      exact I.execution_preserved M x
  | halts k =>
      exact I.clock_preserved M x k
  | poly =>
      exact I.poly_preserved M
  | sat =>
      exact I.sat_preserved x
  | correct =>
      exact I.correct_iff M x
  | neg φ ih =>
      simpa [evalPrime2, evalStd] using not_congr ih
  | and φ ψ ihφ ihψ =>
      simp only [evalPrime2, evalStd]
      exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
      simp only [evalPrime2, evalStd]
      exact or_congr ihφ ihψ

/-- Lemma C: coverage is intentionally restricted to images of standard
candidates and standard inputs.  This avoids a false surjectivity requirement
for arbitrary experimental candidates. -/
def Coverage (I : ConservativePrime2Interpretation) : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ Prime2CorrectAt (I.mapCandidate M) (I.mapInput x)

abbrev MappedPrime2UniversalFailure
    (I : ConservativePrime2Interpretation) : Prop :=
  Coverage I

/-- Full terminal transfer. -/
theorem prime2_G21_transfers_full
    (I : ConservativePrime2Interpretation)
    (hCoverage : Coverage I) :
    G21Pointwise := by
  intro M
  rcases hCoverage M with ⟨x, hx⟩
  exact ⟨x, prime2_failure_transfers I M x hx⟩

/-- For the canonical conservative embedding, Coverage is not weaker than G21:
it is exactly the same mathematical obligation. -/
theorem canonical_coverage_iff_g21 :
    Coverage canonicalInterpretation ↔ G21Pointwise := by
  constructor
  · exact prime2_G21_transfers_full canonicalInterpretation
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, hx⟩

structure Prime2ResearchClosure where
  interpretation : ConservativePrime2Interpretation
  coverage : Coverage interpretation

theorem researchClosure_to_g21
    (R : Prime2ResearchClosure) :
    G21Pointwise :=
  prime2_G21_transfers_full R.interpretation R.coverage

theorem researchClosure_to_p02
    (R : Prime2ResearchClosure) :
    Real.P02TerminalFrontier.P02Target :=
  Real.P02G21G22Attack.g21_pointwise_iff_p02_target.mp
    (researchClosure_to_g21 R)

/-
The fractional/even-nucleus research class may enrich Nucleus metadata or add
separate experimental structures.  Such data cannot affect evalPrime2 for the
standard vocabulary unless a new, separately proved conservative theorem is
provided.  In particular, multiple experimental nucleus tags cannot create a
standard CorrectAt failure.
-/

#print axioms MCore.Research.Prime2.canonical_interpretation_exists
#print axioms MCore.Research.Prime2.prime2_failure_transfers
#print axioms MCore.Research.Prime2.conservative_over_std_vocab
#print axioms MCore.Research.Prime2.prime2_G21_transfers_full
#print axioms MCore.Research.Prime2.canonical_coverage_iff_g21
#print axioms MCore.Research.Prime2.researchClosure_to_g21

end Prime2
end Research
end MCore
