import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02BoundedComputationEncoding

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-!
T5.A1 bounded-computation encoding.

The builder below is intentionally syntactic: it is generated from the finite
transition table, the concrete input, and the fuel.  It does not call TM.run.
The correctness theorem against TM.run is kept as an explicit proposition until
the tableau soundness/completeness proof is kernel checked.
-/

structure Literal where
  var : Nat
  positive : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Literal
abbrev CNF := List Clause

def pos (v : Nat) : Literal := { var := v, positive := true }
def neg (v : Nat) : Literal := { var := v, positive := false }

def literalCircuit (l : Literal) : Circuit :=
  if l.positive then .input l.var else .not (.input l.var)

def clauseCircuit : Clause -> Circuit
  | [] => .const false
  | l :: ls => .or (literalCircuit l) (clauseCircuit ls)

def cnfCircuit : CNF -> Circuit
  | [] => .const true
  | c :: cs => .and (clauseCircuit c) (cnfCircuit cs)

theorem literalCircuit_isClause (l : Literal) :
    IsClause (literalCircuit l) := by
  cases l with
  | mk v p =>
      cases p <;> simp [literalCircuit, IsClause]

theorem clauseCircuit_isClause (c : Clause) :
    IsClause (clauseCircuit c) := by
  induction c with
  | nil =>
      exact emptyClause_isClause
  | cons l ls ih =>
      exact IsClause_or (literalCircuit_isClause l) ih

theorem cnfCircuit_isCNF (f : CNF) :
    IsCNF (cnfCircuit f) := by
  induction f with
  | nil =>
      exact emptyCNF_isCNF
  | cons c cs ih =>
      exact IsCNF_and (isClause_isCNF (clauseCircuit_isClause c)) ih

def evalLiteral (sigma : Assignment) (l : Literal) : Bool :=
  if l.positive then sigma l.var else !(sigma l.var)

def evalClause (sigma : Assignment) : Clause -> Bool
  | [] => false
  | l :: ls => Bool.or (evalLiteral sigma l) (evalClause sigma ls)

def evalCNF (sigma : Assignment) : CNF -> Bool
  | [] => true
  | c :: cs => Bool.and (evalClause sigma c) (evalCNF sigma cs)

theorem eval_literalCircuit
    (sigma : Assignment) (l : Literal) :
    evalCircuit sigma (literalCircuit l) = evalLiteral sigma l := by
  cases l with
  | mk v p =>
      cases p <;> rfl

theorem eval_clauseCircuit
    (sigma : Assignment) (c : Clause) :
    evalCircuit sigma (clauseCircuit c) = evalClause sigma c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      simp [clauseCircuit, evalCircuit, evalClause, eval_literalCircuit, ih]

theorem eval_cnfCircuit
    (sigma : Assignment) (f : CNF) :
    evalCircuit sigma (cnfCircuit f) = evalCNF sigma f := by
  induction f with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [cnfCircuit, evalCircuit, evalCNF, eval_clauseCircuit, ih]

theorem satLanguage_cnfCircuit_iff
    (f : CNF) :
    SATLanguage (cnfCircuit f) ↔ ∃ sigma : Assignment,
      evalCNF sigma f = true := by
  constructor
  · rintro ⟨_hcnf, sigma, hsat⟩
    exact ⟨sigma, by simpa [eval_cnfCircuit] using hsat⟩
  · rintro ⟨sigma, hsat⟩
    refine ⟨cnfCircuit_isCNF f, sigma, ?_⟩
    simpa [eval_cnfCircuit] using hsat

def alphabet : List (Option Bool) :=
  [none, some false, some true]

def symbolCode : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

theorem symbolCode_lt_three (a : Option Bool) :
    symbolCode a < 3 := by
  cases a with
  | none => decide
  | some b =>
      cases b <;> decide

theorem symbolCode_injective :
    ∀ {a b : Option Bool}, symbolCode a = symbolCode b → a = b := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          cases b <;> simp [symbolCode] at h
  | some a =>
      cases a with
      | false =>
          cases b with
          | none => simp [symbolCode] at h
          | some b =>
              cases b with
              | false => rfl
              | true => simp [symbolCode] at h
      | true =>
          cases b with
          | none => simp [symbolCode] at h
          | some b =>
              cases b with
              | false => simp [symbolCode] at h
              | true => rfl

def radius (x : BitString) (t : Nat) : Nat :=
  x.length + t + 1

theorem radius_pos (x : BitString) (t : Nat) :
    0 < radius x t := by
  simp [radius]

def stateCount (M : PolyDTMCandidate) : Nat :=
  M.stateCount + 1

def stateSlots (M : PolyDTMCandidate) (t : Nat) : Nat :=
  (t + 1) * stateCount M

def headBase (M : PolyDTMCandidate) (t : Nat) : Nat :=
  stateSlots M t

def leftBase (M : PolyDTMCandidate) (x : BitString) (t : Nat) : Nat :=
  headBase M t + (t + 1) * 3

def rightBase (M : PolyDTMCandidate) (x : BitString) (t : Nat) : Nat :=
  leftBase M x t + (t + 1) * radius x t * 3

def stateVar
    (M : PolyDTMCandidate) (t s : Nat)
    (q : Fin (M.stateCount + 1)) : Nat :=
  s * stateCount M + q.val

def headVar
    (M : PolyDTMCandidate) (t s : Nat)
    (a : Option Bool) : Nat :=
  headBase M t + s * 3 + symbolCode a

def leftVar
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  leftBase M x t +
    (s * radius x t + i) * 3 + symbolCode a

def rightVar
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  rightBase M x t +
    (s * radius x t + i) * 3 + symbolCode a

def litFor (v : Nat) (value : Bool) : Literal :=
  if value then pos v else neg v

def setStateClauses
    (guard : Clause)
    (M : PolyDTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) : CNF :=
  (List.ofFn fun q : Fin (M.stateCount + 1) =>
    guard ++ [litFor (stateVar M t s q) (decide (q = target))])

def setSymbolClauses
    (guard : Clause)
    (varAt : Option Bool -> Nat)
    (target : Option Bool) : CNF :=
  alphabet.map fun a =>
    guard ++ [litFor (varAt a) (decide (a = target))]

def copySymbolClauses
    (guard : Clause)
    (oldVar newVar : Option Bool -> Nat) : CNF :=
  alphabet.flatMap fun a =>
    [ guard ++ [neg (oldVar a), pos (newVar a)]
    , guard ++ [pos (oldVar a), neg (newVar a)] ]

def copyLeftAll
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) : CNF :=
  (List.range (radius x t)).flatMap fun i =>
    copySymbolClauses guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i)

def copyRightAll
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) : CNF :=
  (List.range (radius x t)).flatMap fun i =>
    copySymbolClauses guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i)

def setLeftCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : CNF :=
  setSymbolClauses guard (leftVar M x t s i) target

def setRightCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : CNF :=
  setSymbolClauses guard (rightVar M x t s i) target

def copyLeftCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : CNF :=
  copySymbolClauses guard
    (leftVar M x t oldS oldI)
    (leftVar M x t newS newI)

def copyRightCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : CNF :=
  copySymbolClauses guard
    (rightVar M x t oldS oldI)
    (rightVar M x t newS newI)

def copyHeadCell
    (guard : Clause)
    (M : PolyDTMCandidate) (t oldS newS : Nat) : CNF :=
  copySymbolClauses guard
    (headVar M t oldS)
    (headVar M t newS)

def initialCNF
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : CNF :=
  let tape := inputTape x
  let statePart :=
    setStateClauses [] M t 0 M.machine.initial
  let headPart :=
    setSymbolClauses [] (headVar M t 0) tape.head
  let leftPart :=
    (List.range (radius x t)).flatMap fun i =>
      setLeftCell [] M x t 0 i
        (tape.left.getD i M.machine.blank)
  let rightPart :=
    (List.range (radius x t)).flatMap fun i =>
      setRightCell [] M x t 0 i
        (tape.right.getD i M.machine.blank)
  statePart ++ headPart ++ leftPart ++ rightPart

def haltingCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) : CNF :=
  let guard := [neg (stateVar M t s q), neg (headVar M t s a)]
  setStateClauses guard M t (s + 1) q ++
  copyHeadCell guard M t s (s + 1) ++
  copyLeftAll guard M x t s ++
  copyRightAll guard M x t s

def stayCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : CNF :=
  let guard := [neg (stateVar M t s q), neg (headVar M t s a)]
  setStateClauses guard M t (s + 1) qNext ++
  setSymbolClauses guard (headVar M t (s + 1)) write ++
  copyLeftAll guard M x t s ++
  copyRightAll guard M x t s

def leftMoveCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : CNF :=
  let guard := [neg (stateVar M t s q), neg (headVar M t s a)]
  let r := radius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      copyLeftCell guard M x t (s) (i + 1) (s + 1) i
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      copyRightCell guard M x t (s) i (s + 1) (i + 1)
  setStateClauses guard M t (s + 1) qNext ++
  copySymbolClauses guard
    (leftVar M x t s 0)
    (headVar M t (s + 1)) ++
  shiftedLeft ++
  setLeftCell guard M x t (s + 1) (r - 1) M.machine.blank ++
  setRightCell guard M x t (s + 1) 0 write ++
  shiftedRight

def rightMoveCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : CNF :=
  let guard := [neg (stateVar M t s q), neg (headVar M t s a)]
  let r := radius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      copyLeftCell guard M x t (s) i (s + 1) (i + 1)
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      copyRightCell guard M x t (s) (i + 1) (s + 1) i
  setStateClauses guard M t (s + 1) qNext ++
  copySymbolClauses guard
    (rightVar M x t s 0)
    (headVar M t (s + 1)) ++
  setLeftCell guard M x t (s + 1) 0 write ++
  shiftedLeft ++
  shiftedRight ++
  setRightCell guard M x t (s + 1) (r - 1) M.machine.blank

def transitionCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) : CNF :=
  if hhalt : M.machine.halting q = true then
    haltingCaseCNF M x t s q a
  else
    match M.machine.transition q a with
    | (qNext, write, .stay) =>
        stayCaseCNF M x t s q a qNext write
    | (qNext, write, .left) =>
        leftMoveCaseCNF M x t s q a qNext write
    | (qNext, write, .right) =>
        rightMoveCaseCNF M x t s q a qNext write

def transitionStepCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) : CNF :=
  (List.ofFn fun q : Fin (M.stateCount + 1) =>
    alphabet.flatMap fun a =>
      transitionCaseCNF M x t s q a).flatten

def transitionsCNF
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : CNF :=
  (List.range t).flatMap fun s =>
    transitionStepCNF M x t s

def acceptingStateLits
    (M : PolyDTMCandidate) (t : Nat) : Clause :=
  (List.ofFn fun q : Fin (M.stateCount + 1) => q).filterMap fun q =>
    if M.accepting q = true then
      some (pos (stateVar M t t q))
    else
      none

def finalAcceptanceCNF
    (M : PolyDTMCandidate) (t : Nat) : CNF :=
  [acceptingStateLits M t]

/-- Genuine local tableau builder.  No invocation of TM.run occurs in this
definition or any construction dependency above it. -/
def boundedExecTableauCNF
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : CNF :=
  initialCNF M x t ++
  transitionsCNF M x t ++
  finalAcceptanceCNF M t

def boundedExecCircuit
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : Circuit :=
  cnfCircuit (boundedExecTableauCNF M x t)

theorem boundedExecCircuit_isCNF
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    IsCNF (boundedExecCircuit M x t) := by
  exact cnfCircuit_isCNF _

def boundedExecBits
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : BitString :=
  encodeCircuit (boundedExecCircuit M x t)

theorem boundedExecBits_valid
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    ∃ phi : Circuit,
      decodeCircuit (boundedExecBits M x t) = some phi := by
  exact ⟨boundedExecCircuit M x t, decodeCircuit_encode _⟩

def AcceptsAtFuel
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) : Prop :=
  M.accepting
    (M.machine.run t (initialTMConfig M.machine x)).state = true

/-- Exact A1 theorem still to be discharged by tableau soundness/completeness.
It is a proposition, not an assumption or axiom. -/
def BoundedExecCorrectness : Prop :=
  ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat),
    SATLanguage (boundedExecCircuit M x t) ↔
      AcceptsAtFuel M x t

theorem boundedExecBits_sat_iff_circuit_sat
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    SATBits circuitBitEncoding (boundedExecBits M x t) ↔
      SATLanguage (boundedExecCircuit M x t) := by
  exact encoded_sat_equivalence _

/-- Once the tableau correctness theorem is supplied, canonical SAT bits expose
the same bounded execution semantics. -/
theorem boundedExecCorrectness_to_bits
    (h : BoundedExecCorrectness)
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    SATBits circuitBitEncoding (boundedExecBits M x t) <->
      AcceptsAtFuel M x t := by
  rw [boundedExecBits_sat_iff_circuit_sat]
  exact h M x t

#print axioms MCore.Real.P02BoundedComputationEncoding.literalCircuit_isClause
#print axioms MCore.Real.P02BoundedComputationEncoding.clauseCircuit_isClause
#print axioms MCore.Real.P02BoundedComputationEncoding.cnfCircuit_isCNF
#print axioms MCore.Real.P02BoundedComputationEncoding.satLanguage_cnfCircuit_iff
#print axioms MCore.Real.P02BoundedComputationEncoding.boundedExecCircuit_isCNF
#print axioms MCore.Real.P02BoundedComputationEncoding.boundedExecBits_valid
#print axioms MCore.Real.P02BoundedComputationEncoding.boundedExecBits_sat_iff_circuit_sat
#print axioms MCore.Real.P02BoundedComputationEncoding.boundedExecCorrectness_to_bits

end P02BoundedComputationEncoding
end Real
end MCore
