import MCore.K10

namespace Audit.SAT

structure Literal (n : Nat) where
  var : Fin n
  negated : Bool
  deriving DecidableEq, Repr

abbrev Clause (n : Nat) := List (Literal n)

structure CNF where
  nvars : Nat
  clauses : List (Clause nvars)
  deriving Repr

abbrev Valuation (n : Nat) := Fin n → Bool

def evalLiteral {n : Nat} (v : Valuation n) (l : Literal n) : Bool :=
  if l.negated then !(v l.var) else v l.var

def evalClause {n : Nat} (v : Valuation n) (c : Clause n) : Bool :=
  c.any (evalLiteral v)

def evalCNF (φ : CNF) (v : Valuation φ.nvars) : Bool :=
  φ.clauses.all (evalClause v)

def Satisfiable (φ : CNF) : Prop :=
  ∃ v : Valuation φ.nvars, evalCNF φ v = true

def SATVerifier (φ : CNF) (w : Valuation φ.nvars) : Bool :=
  evalCNF φ w

theorem sat_verifier_correct (φ : CNF) :
    Satisfiable φ ↔
      ∃ w : Valuation φ.nvars, SATVerifier φ w = true := by
  rfl

def witnessBitLength (φ : CNF) : Nat := φ.nvars

theorem witness_length_exact (φ : CNF) :
    witnessBitLength φ = φ.nvars := rfl

def Is3CNF (φ : CNF) : Prop :=
  ∀ c ∈ φ.clauses, c.length ≤ 3

def ThreeSatisfiable (φ : CNF) : Prop :=
  Is3CNF φ ∧ Satisfiable φ

theorem three_sat_implies_sat {φ : CNF} :
    ThreeSatisfiable φ → Satisfiable φ :=
  And.right

/-- Internal semantic certificate only. No bitstring encoding, machine runtime,
or NP-completeness theorem is smuggled into this structure. -/
structure SATSemanticCertificate where
  verifierCorrect :
    ∀ φ : CNF,
      Satisfiable φ ↔
        ∃ w : Valuation φ.nvars, SATVerifier φ w = true

def semanticCertificate : SATSemanticCertificate :=
  { verifierCorrect := sat_verifier_correct }

def SATSemanticStatus : String := "PROVED_INTERNAL"
def SATEncodingStatus : String := "OPEN_FORMALIZATION"
def SATMachineRealizationStatus : String := "OPEN_FORMALIZATION"
def CookLevinStatus : String := "EXTERNAL_CLASSICAL_PENDING_MATCH"

#print axioms Audit.SAT.sat_verifier_correct
#print axioms Audit.SAT.three_sat_implies_sat

end Audit.SAT
