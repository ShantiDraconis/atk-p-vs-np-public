import MCore.Real.Model

namespace MCore.Real

inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving DecidableEq, Repr

abbrev Clause := List Literal
abbrev CNF := List Clause

structure Assignment where
  bits : List Bool
  deriving DecidableEq, Repr

namespace Assignment

def value (a : Assignment) (idx : Nat) : Bool :=
  a.bits.getD idx false

end Assignment

def evalLiteral (a : Assignment) : Literal → Bool
  | .pos v => a.value v
  | .neg v => !(a.value v)

def evalClause (a : Assignment) (clause : Clause) : Bool :=
  clause.any (evalLiteral a)

def evalCNF (a : Assignment) (cnf : CNF) : Bool :=
  cnf.all (evalClause a)

def literalIndex : Literal → Nat
  | .pos v => v
  | .neg v => v

def varsInClause (clause : Clause) : Nat :=
  clause.foldl (fun m lit => Nat.max m (literalIndex lit + 1)) 0

def numVars (cnf : CNF) : Nat :=
  cnf.foldl (fun m clause => Nat.max m (varsInClause clause)) 0

def encodeNatUnary (n : Nat) : List Char :=
  List.replicate n '1' ++ ['0']

private def parseNatUnaryAux (acc : Nat) : List Char → Option (Nat × List Char)
  | '1' :: rest => parseNatUnaryAux (acc + 1) rest
  | '0' :: rest => some (acc, rest)
  | _ => none

def parseNatUnary : List Char → Option (Nat × List Char) :=
  parseNatUnaryAux 0

def encodeLiteral : Literal → List Char
  | .pos v => 'P' :: encodeNatUnary v
  | .neg v => 'N' :: encodeNatUnary v

def parseLiteral : List Char → Option (Literal × List Char)
  | 'P' :: rest => do
      let (v, tail) ← parseNatUnary rest
      pure (.pos v, tail)
  | 'N' :: rest => do
      let (v, tail) ← parseNatUnary rest
      pure (.neg v, tail)
  | _ => none

private def encodeLiterals : Clause → List Char
  | [] => []
  | lit :: [] => encodeLiteral lit
  | lit :: rest => encodeLiteral lit ++ ',' :: encodeLiterals rest

def encodeClause (clause : Clause) : List Char :=
  '[' :: encodeLiterals clause ++ [']']

private def encodeClauses : CNF → List Char
  | [] => []
  | clause :: [] => encodeClause clause
  | clause :: rest => encodeClause clause ++ ';' :: encodeClauses rest

def encodeCNFChars (cnf : CNF) : List Char :=
  '{' :: encodeClauses cnf ++ ['}']

def encodeCNF (cnf : CNF) : String :=
  String.mk (encodeCNFChars cnf)

private def parseLiteralList : List Char → Option (Clause × List Char)
  | ']' :: rest => some ([], rest)
  | chars => do
      let (lit, rest) ← parseLiteral chars
      match rest with
      | ',' :: tail => do
          let (lits, tail') ← parseLiteralList tail
          pure (lit :: lits, tail')
      | ']' :: tail => pure ([lit], tail)
      | _ => none

private def parseClause : List Char → Option (Clause × List Char)
  | '[' :: rest => parseLiteralList rest
  | _ => none

private def parseCNFList : List Char → Option (CNF × List Char)
  | '}' :: rest => some ([], rest)
  | chars => do
      let (clause, rest) ← parseClause chars
      match rest with
      | ';' :: tail => do
          let (clauses, tail') ← parseCNFList tail
          pure (clause :: clauses, tail')
      | '}' :: tail => pure ([clause], tail)
      | _ => none

def parseCNFChars : List Char → Option (CNF × List Char)
  | '{' :: rest => parseCNFList rest
  | _ => none

def parseCNF (s : String) : Option CNF :=
  match parseCNFChars s.data with
  | some (cnf, []) => some cnf
  | _ => none

def WellFormedCNFString (s : String) : Prop :=
  ∃ cnf, parseCNF s = some cnf

def SemanticallyRepresents (s : String) (a : Assignment) (b : Bool) : Prop :=
  ∃ cnf, parseCNF s = some cnf ∧ evalCNF a cnf = b

private theorem parseNatUnaryAux_replicate (acc n : Nat) (rest : List Char) :
    parseNatUnaryAux acc (List.replicate n '1' ++ '0' :: rest) = some (acc + n, rest) := by
  induction n generalizing acc with
  | zero => simp [parseNatUnaryAux]
  | succ n ih =>
      simp [parseNatUnaryAux, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem parseNatUnary_encode (n : Nat) (rest : List Char) :
    parseNatUnary (encodeNatUnary n ++ rest) = some (n, rest) := by
  simpa [parseNatUnary, encodeNatUnary, List.append_assoc] using
    parseNatUnaryAux_replicate 0 n rest

theorem parseLiteral_encode (lit : Literal) (rest : List Char) :
    parseLiteral (encodeLiteral lit ++ rest) = some (lit, rest) := by
  cases lit with
  | pos v =>
      simp [encodeLiteral, parseLiteral, parseNatUnary_encode, List.append_assoc]
  | neg v =>
      simp [encodeLiteral, parseLiteral, parseNatUnary_encode, List.append_assoc]

private theorem parseLiteralList_encode (lits : Clause) (rest : List Char) :
    parseLiteralList (encodeLiterals lits ++ ']' :: rest) = some (lits, rest) := by
  induction lits with
  | nil => simp [encodeLiterals, parseLiteralList]
  | cons lit tail ih =>
      cases tail with
      | nil =>
          simp [encodeLiterals, parseLiteralList, parseLiteral_encode]
      | cons lit' tail' =>
          simp [encodeLiterals, parseLiteralList, parseLiteral_encode, ih, List.append_assoc]

private theorem parseClause_encode (clause : Clause) (rest : List Char) :
    parseClause (encodeClause clause ++ rest) = some (clause, rest) := by
  simp [encodeClause, parseClause, parseLiteralList_encode, List.append_assoc]

private theorem parseCNFList_encode (cnf : CNF) (rest : List Char) :
    parseCNFList (encodeClauses cnf ++ '}' :: rest) = some (cnf, rest) := by
  induction cnf with
  | nil => simp [encodeClauses, parseCNFList]
  | cons clause tail ih =>
      cases tail with
      | nil =>
          simp [encodeClauses, parseCNFList, parseClause_encode, List.append_assoc]
      | cons c tail' =>
          simp [encodeClauses, parseCNFList, parseClause_encode, ih, List.append_assoc]

theorem parseCNF_encode (cnf : CNF) :
    parseCNF (encodeCNF cnf) = some cnf := by
  simp [parseCNF, encodeCNF, encodeCNFChars, parseCNFChars, parseCNFList_encode, List.append_assoc]

theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro a b h
  have ha : parseCNF (encodeCNF a) = some a := parseCNF_encode a
  have hb : parseCNF (encodeCNF b) = some b := parseCNF_encode b
  rw [h] at ha
  exact Option.some.inj (ha.trans hb.symm)

theorem wellFormed_exact (s : String) :
    WellFormedCNFString s ↔ ∃ cnf, parseCNF s = some cnf := Iff.rfl

theorem semanticallyRepresents_exact (s : String) (a : Assignment) (b : Bool) :
    SemanticallyRepresents s a b ↔ ∃ cnf, parseCNF s = some cnf ∧ evalCNF a cnf = b := Iff.rfl

theorem parseCNF_negativeControl_empty : parseCNF "" = none := rfl

theorem parseCNF_negativeControl_badPrefix : parseCNF "X" = none := rfl

theorem wellFormed_of_encode (cnf : CNF) : WellFormedCNFString (encodeCNF cnf) := by
  exact ⟨cnf, parseCNF_encode cnf⟩

def allAssignments : Nat → List Assignment
  | 0 => [⟨[]⟩]
  | n + 1 =>
      let prev := allAssignments n
      (prev.map fun a => ⟨false :: a.bits⟩) ++
      (prev.map fun a => ⟨true :: a.bits⟩)

inductive SATState where
  | start
  | verify (cnf : CNF)
  | accept
  | reject
  deriving DecidableEq, Repr

inductive SATSymbol where
  | input (s : String)
  | witness (bits : List Bool)
  | blank
  deriving DecidableEq, Repr

def satInitialConfiguration (s : String) : Configuration SATState SATSymbol :=
  { state := .start
    tape := { left := [], head := .input s, right := [] } }

def satTransition : SATState → SATSymbol → List (SATState × SATSymbol × Direction)
  | .start, .input s =>
      match parseCNF s with
      | none => [(.reject, .input s, .stay)]
      | some cnf =>
          (allAssignments (numVars cnf)).map fun a => (.verify cnf, .witness a.bits, .stay)
  | .verify cnf, .witness bits =>
      let a : Assignment := ⟨bits⟩
      if evalCNF a cnf then
        [(.accept, .witness bits, .stay)]
      else
        [(.reject, .witness bits, .stay)]
  | .start, _ => [(.reject, .blank, .stay)]
  | .verify _, _ => [(.reject, .blank, .stay)]
  | .accept, sym => [(.accept, sym, .stay)]
  | .reject, sym => [(.reject, sym, .stay)]

def satVerifier : NTM SATState SATSymbol :=
  { initial := .start
    blank := .blank
    transition := satTransition
    accepting := fun st =>
      match st with
      | .accept => true
      | _ => false
    rejecting := fun st =>
      match st with
      | .reject => true
      | _ => false }

def satVerifyConfig (cnf : CNF) (bits : List Bool) : Configuration SATState SATSymbol :=
  { state := .verify cnf
    tape := { left := [], head := .witness bits, right := [] } }

def satAcceptConfig (bits : List Bool) : Configuration SATState SATSymbol :=
  { state := .accept
    tape := { left := [], head := .witness bits, right := [] } }

def satRejectConfig (bits : List Bool) : Configuration SATState SATSymbol :=
  { state := .reject
    tape := { left := [], head := .witness bits, right := [] } }

def satInputRejectConfig (s : String) : Configuration SATState SATSymbol :=
  { state := .reject
    tape := { left := [], head := .input s, right := [] } }

def SATLanguage (s : String) : Prop :=
  ∃ cnf, parseCNF s = some cnf ∧
    ∃ a ∈ allAssignments (numVars cnf), evalCNF a cnf = true

private lemma runBranches_two (s : String) :
    satVerifier.runBranches 2 [satInitialConfiguration s] =
      match parseCNF s with
      | none => [satInputRejectConfig s]
      | some cnf =>
          (allAssignments (numVars cnf)).map fun a =>
            if evalCNF a cnf then satAcceptConfig a.bits else satRejectConfig a.bits := by
  simp [NTM.runBranches, NTM.successors, NTM.stepBranch, satVerifier, satTransition,
    satInitialConfiguration, satVerifyConfig, satAcceptConfig, satRejectConfig, satInputRejectConfig]

theorem sat_acceptsWithin_two_of_language {s : String} :
    SATLanguage s → satVerifier.AcceptsWithin 2 (satInitialConfiguration s) := by
  intro hs
  rcases hs with ⟨cnf, hparse, a, haMem, haEval⟩
  refine ⟨satAcceptConfig a.bits, ?_, by simp [satVerifier, satAcceptConfig]⟩
  rw [runBranches_two, hparse]
  refine List.mem_map_of_mem _ haMem
  simp [haEval, satAcceptConfig, satRejectConfig]

theorem sat_language_of_acceptsWithin_two {s : String} :
    satVerifier.AcceptsWithin 2 (satInitialConfiguration s) → SATLanguage s := by
  intro hacc
  rcases hacc with ⟨reached, hreached, haccept⟩
  rw [runBranches_two] at hreached
  cases hparse : parseCNF s with
  | none =>
      simp [hparse, satInputRejectConfig, satVerifier] at hreached haccept
  | some cnf =>
      simp [hparse] at hreached
      rcases List.mem_map.mp hreached with ⟨a, haMem, hreachedEq⟩
      refine ⟨cnf, hparse, a, haMem, ?_⟩
      have haccState : reached.state = .accept := by
        simpa [satVerifier] using haccept
      rw [hreachedEq] at haccState
      by_cases hEval : evalCNF a cnf
      · simpa [hEval, satAcceptConfig, satRejectConfig] using haccState
      · simp [hEval, satAcceptConfig, satRejectConfig] at haccState

theorem sat_sound_complete (s : String) :
    satVerifier.AcceptsWithin 2 (satInitialConfiguration s) ↔ SATLanguage s := by
  constructor
  · exact sat_language_of_acceptsWithin_two
  · exact sat_acceptsWithin_two_of_language

theorem sat_uniform_halting :
    ∀ s : String, satVerifier.HaltsWithin 2 (satInitialConfiguration s) := by
  intro s reached hreached
  rw [runBranches_two] at hreached
  cases hparse : parseCNF s with
  | none =>
      simp [hparse, satVerifier, satInputRejectConfig] at hreached
      subst hreached
      right
      simp [satVerifier]
  | some cnf =>
      simp [hparse] at hreached
      rcases List.mem_map.mp hreached with ⟨a, haMem, hreachedEq⟩
      subst hreachedEq
      by_cases hEval : evalCNF a cnf
      · left
        simp [satVerifier, satAcceptConfig, satRejectConfig, hEval]
      · right
        simp [satVerifier, satAcceptConfig, satRejectConfig, hEval]

def satRuntime : TimeBound :=
  fun _ => 2

structure PolyBound (T : TimeBound) : Prop where
  c : Nat
  k : Nat
  c_pos : 0 < c
  bound : ∀ n, T n ≤ c * (n + 1) ^ k

structure DecidesWithin
    {State Symbol : Type}
    (machine : NTM State Symbol)
    (init : String → Configuration State Symbol)
    (language : String → Prop)
    (runtime : TimeBound) : Prop where
  sound_complete : ∀ s, machine.AcceptsWithin (runtime s.length) (init s) ↔ language s
  halts : ∀ s, machine.HaltsWithin (runtime s.length) (init s)

lemma satRuntime_poly : PolyBound satRuntime := by
  refine ⟨2, 1, by decide, ?_⟩
  intro n
  simp [satRuntime]

lemma satRuntime_matches_two (s : String) : satRuntime s.length = 2 := rfl

theorem sat_decidesWithin :
    DecidesWithin satVerifier satInitialConfiguration SATLanguage satRuntime := by
  refine ⟨?_, ?_⟩
  · intro s
    simpa [satRuntime_matches_two] using sat_sound_complete s
  · intro s
    simpa [satRuntime_matches_two] using sat_uniform_halting s

theorem SATNPRealization :
    DecidesWithin satVerifier satInitialConfiguration SATLanguage satRuntime ∧ PolyBound satRuntime := by
  exact ⟨sat_decidesWithin, satRuntime_poly⟩

end MCore.Real
