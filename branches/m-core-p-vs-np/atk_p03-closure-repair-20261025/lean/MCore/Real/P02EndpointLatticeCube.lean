import MCore.Real.P02EndpointLattice

namespace MCore
namespace Real
namespace P02EndpointLatticeCube

open P02EndpointLattice
open P02RPADualConfirmation

inductive EndpointAtom
  | O
  | C
  deriving DecidableEq, Repr

abbrev EndpointWord := List EndpointAtom

def evalWord : EndpointWord → MultiEndpointState
  | [] => emptyMulti
  | .O :: xs => openMulti + evalWord xs
  | .C :: xs => closedMulti + evalWord xs

def W_OPEN : EndpointWord := [.O]
def W_CLOSED : EndpointWord := [.C]

def W_OC : EndpointWord := [.O, .C]
def W_CO : EndpointWord := [.C, .O]
def W_OO : EndpointWord := [.O, .O]
def W_CC : EndpointWord := [.C, .C]

def W_OOO : EndpointWord := [.O, .O, .O]
def W_CCC : EndpointWord := [.C, .C, .C]
def W_OOC : EndpointWord := [.O, .O, .C]
def W_OCO : EndpointWord := [.O, .C, .O]
def W_COO : EndpointWord := [.C, .O, .O]
def W_OCC : EndpointWord := [.O, .C, .C]
def W_COC : EndpointWord := [.C, .O, .C]
def W_CCO : EndpointWord := [.C, .C, .O]

def W_FULL4 : EndpointWord := [.O, .O, .C, .C]

@[simp] theorem eval_OPEN : evalWord W_OPEN = ⟨1,0⟩ := rfl
@[simp] theorem eval_CLOSED : evalWord W_CLOSED = ⟨0,1⟩ := rfl

@[simp] theorem eval_OC : evalWord W_OC = ⟨1,1⟩ := rfl
@[simp] theorem eval_CO : evalWord W_CO = ⟨1,1⟩ := rfl
@[simp] theorem eval_OO : evalWord W_OO = ⟨2,0⟩ := rfl
@[simp] theorem eval_CC : evalWord W_CC = ⟨0,2⟩ := rfl

@[simp] theorem eval_OOO : evalWord W_OOO = ⟨3,0⟩ := rfl
@[simp] theorem eval_CCC : evalWord W_CCC = ⟨0,3⟩ := rfl
@[simp] theorem eval_OOC : evalWord W_OOC = ⟨2,1⟩ := rfl
@[simp] theorem eval_OCO : evalWord W_OCO = ⟨2,1⟩ := rfl
@[simp] theorem eval_COO : evalWord W_COO = ⟨2,1⟩ := rfl
@[simp] theorem eval_OCC : evalWord W_OCC = ⟨1,2⟩ := rfl
@[simp] theorem eval_COC : evalWord W_COC = ⟨1,2⟩ := rfl
@[simp] theorem eval_CCO : evalWord W_CCO = ⟨1,2⟩ := rfl

@[simp] theorem eval_FULL4 : evalWord W_FULL4 = ⟨2,2⟩ := rfl

/-- All 14 nonempty ordered words up to length 3. -/
def cube14 : List EndpointWord :=
  [ W_OPEN, W_CLOSED,
    W_OC, W_CO, W_OO, W_CC,
    W_OOO, W_CCC, W_OOC, W_OCO, W_COO, W_OCC, W_COC, W_CCO ]

theorem cube14_length : cube14.length = 14 := by
  rfl

theorem cube14_pair_states :
    evalWord W_OC = dualMulti ∧
    evalWord W_CO = dualMulti ∧
    evalWord W_OO = ⟨2,0⟩ ∧
    evalWord W_CC = ⟨0,2⟩ := by
  decide

theorem cube14_triple_states :
    evalWord W_OOO = ⟨3,0⟩ ∧
    evalWord W_CCC = ⟨0,3⟩ ∧
    evalWord W_OOC = ⟨2,1⟩ ∧
    evalWord W_OCO = ⟨2,1⟩ ∧
    evalWord W_COO = ⟨2,1⟩ ∧
    evalWord W_OCC = ⟨1,2⟩ ∧
    evalWord W_COC = ⟨1,2⟩ ∧
    evalWord W_CCO = ⟨1,2⟩ := by
  decide

/-- Order is preserved syntactically at the word level even when multiplicity
evaluation identifies permutations. -/
theorem ordered_words_distinct_examples :
    W_OOC ≠ W_OCO ∧ W_OCO ≠ W_COO ∧
    W_OCC ≠ W_COC ∧ W_COC ≠ W_CCO := by
  decide

/-- Idempotent canonicalization collapses every mixed triple to FULL. -/
theorem mixed_triples_canonicalize_full :
    canonicalize (evalWord W_OOC) = FULL ∧
    canonicalize (evalWord W_OCO) = FULL ∧
    canonicalize (evalWord W_COO) = FULL ∧
    canonicalize (evalWord W_OCC) = FULL ∧
    canonicalize (evalWord W_COC) = FULL ∧
    canonicalize (evalWord W_CCO) = FULL := by
  decide

/-- Pure triples collapse to their corresponding canonical side. -/
theorem pure_triples_canonicalize :
    canonicalize (evalWord W_OOO) = OPEN ∧
    canonicalize (evalWord W_CCC) = CLOSED := by
  decide

/-- FULL = OPEN+OPEN+CLOSED+CLOSED at multiplicity level and canonicalizes
to the maximal dual state. -/
theorem full4_canonicalizes_full :
    canonicalize (evalWord W_FULL4) = FULL := by
  decide

/-- Publication-facing certificate object for the maximal FULL state. -/
structure FullWordCertificate where
  word : EndpointWord
  word_is_full : word = W_FULL4
  external : GLOBAL_EXTERNAL_CERTIFICATE

theorem fullWordCertificate_iff_globalExternal :
    Nonempty FullWordCertificate ↔ GLOBAL_EXTERNAL_CERTIFICATE := by
  constructor
  · rintro ⟨c⟩
    exact c.external
  · intro h
    exact ⟨{ word := W_FULL4, word_is_full := rfl, external := h }⟩

theorem fullWordCertificate_iff_math :
    Nonempty FullWordCertificate ↔ MATH := by
  rw [fullWordCertificate_iff_globalExternal]

#print axioms MCore.Real.P02EndpointLatticeCube.cube14_length
#print axioms MCore.Real.P02EndpointLatticeCube.cube14_pair_states
#print axioms MCore.Real.P02EndpointLatticeCube.cube14_triple_states
#print axioms MCore.Real.P02EndpointLatticeCube.ordered_words_distinct_examples
#print axioms MCore.Real.P02EndpointLatticeCube.mixed_triples_canonicalize_full
#print axioms MCore.Real.P02EndpointLatticeCube.pure_triples_canonicalize
#print axioms MCore.Real.P02EndpointLatticeCube.full4_canonicalizes_full
#print axioms MCore.Real.P02EndpointLatticeCube.fullWordCertificate_iff_globalExternal
#print axioms MCore.Real.P02EndpointLatticeCube.fullWordCertificate_iff_math

end P02EndpointLatticeCube
end Real
end MCore
