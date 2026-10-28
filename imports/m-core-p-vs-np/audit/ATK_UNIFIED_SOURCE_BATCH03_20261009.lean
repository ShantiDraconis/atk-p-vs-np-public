/- ATK BATCH03: complete sourced modules, archival concatenation, not a Lean compilation certificate. -/

/- SOURCE lean/MCore/Real/CNFStructure.lean BLOB 83bfd6b26efc506c97f9f2328e0f7996fb44e434 -/
import MCore.C12.Families

namespace MCore
namespace Real

open CircuitK1
open C12

/-- A propositional literal in the existing Circuit AST. -/
def IsLiteral : Circuit → Prop
  | .input _ => True
  | .not (.input _) => True
  | _ => False

/-- A clause is a literal, an OR-tree of clauses, or the empty clause `false`. -/
def IsClause : Circuit → Prop
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause a ∧ IsClause b
  | _ => False

/-- CNF is a clause, an AND-tree of CNFs, or an empty conjunction/empty clause. -/
def IsCNF : Circuit → Prop
  | .const true => True
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause (.or a b)
  | .and a b => IsCNF a ∧ IsCNF b
  | _ => False

@[simp] theorem isLiteral_input (i : Nat) :
    IsLiteral (.input i) := trivial

@[simp] theorem isLiteral_not_input (i : Nat) :
    IsLiteral (.not (.input i)) := trivial

@[simp] theorem emptyClause_isClause :
    IsClause (.const false) := trivial

@[simp] theorem emptyCNF_isCNF :
    IsCNF (.const true) := trivial

@[simp] theorem emptyClause_isCNF :
    IsCNF (.const false) := trivial

/-- Structural closure of clauses under disjunction. -/
theorem IsClause_or {a b : Circuit} (ha : IsClause a) (hb : IsClause b) :
    IsClause (.or a b) :=
  ⟨ha, hb⟩

/-- Structural closure of CNFs under conjunction. -/
theorem IsCNF_and {a b : Circuit} (ha : IsCNF a) (hb : IsCNF b) :
    IsCNF (.and a b) :=
  ⟨ha, hb⟩

/-- Every structural literal is also a clause. -/
theorem isLiteral_isClause {c : Circuit} (h : IsLiteral c) : IsClause c := by
  cases c with
  | input i => exact True.intro
  | const b => cases h
  | not c =>
      cases c with
      | input i => exact True.intro
      | const b => cases h
      | not c => cases h
      | and a b => cases h
      | or a b => cases h
  | and a b => cases h
  | or a b => cases h

/-- Every literal produced by C12.literalAt has literal shape. -/
theorem literalAt_isLiteral
    (nVars seed clauseIdx pos : Nat) :
    IsLiteral (C12.literalAt nVars seed clauseIdx pos) := by
  unfold C12.literalAt
  refine Decidable.byCases
    (p := (seed + clauseIdx + pos) % 2 = 0) ?_ ?_
  · intro h
    rw [if_pos h]
    exact True.intro
  · intro h
    rw [if_neg h]
    exact True.intro

/-- Every literal produced by C12.literalAt is structurally a clause. -/
theorem literalAt_isClause
    (nVars seed clauseIdx pos : Nat) :
    IsClause (C12.literalAt nVars seed clauseIdx pos) :=
  isLiteral_isClause (literalAt_isLiteral nVars seed clauseIdx pos)


/-- Folding disjunction over clauses preserves clause shape from a clause accumulator. -/
theorem foldl_or_preserves_isClause
    (xs : List Circuit) (acc : Circuit)
    (hacc : IsClause acc)
    (hxs : ∀ c ∈ xs, IsClause c) :
    IsClause (xs.foldl (fun a c => .or a c) acc) := by
  induction xs generalizing acc with
  | nil =>
      exact hacc
  | cons x xs ih =>
      have hx : IsClause x :=
        hxs x (List.Mem.head xs)
      have htail : ∀ c ∈ xs, IsClause c := by
        intro c hc
        exact hxs c (List.Mem.tail x hc)
      exact ih (.or acc x) (IsClause_or hacc hx) htail

/-- Every nonempty randomClause has clause shape. -/
theorem randomClause_isClause
    (nVars seed clauseIdx width : Nat)
    (hwidth : 0 < width) :
    IsClause (C12.randomClause nVars seed clauseIdx width) := by
  unfold C12.randomClause
  cases width with
  | zero =>
      cases Nat.not_lt_zero 0 hwidth
  | succ width =>
      have loop_append_single :
          ∀ (n : Nat) (acc : List Nat) (b : Nat),
            List.range.loop n (acc ++ [b]) =
              List.range.loop n acc ++ [b] := by
        intro n
        induction n with
        | zero =>
            intro acc b
            rfl
        | succ m ih =>
            intro acc b
            calc
              List.range.loop (Nat.succ m) (acc ++ [b])
                  = List.range.loop m (m :: (acc ++ [b])) := rfl
              _ = List.range.loop m ((m :: acc) ++ [b]) := rfl
              _ = List.range.loop m (m :: acc) ++ [b] := ih (m :: acc) b
              _ = List.range.loop (Nat.succ m) acc ++ [b] := rfl
      have range_append :
          ∀ n : Nat,
            List.range (Nat.succ n) = List.range n ++ [n] := by
        intro n
        calc
          List.range (Nat.succ n)
              = List.range.loop (Nat.succ n) [] := rfl
          _ = List.range.loop n [n] := rfl
          _ = List.range.loop n ([] ++ [n]) := rfl
          _ = List.range.loop n [] ++ [n] := loop_append_single n [] n
          _ = List.range n ++ [n] := rfl
      have map_succ_append :
          ∀ (l₁ l₂ : List Nat),
            List.map Nat.succ (l₁ ++ l₂) =
              List.map Nat.succ l₁ ++ List.map Nat.succ l₂ := by
        intro l₁
        induction l₁ with
        | nil =>
            intro l₂
            rfl
        | cons x xs ih =>
            intro l₂
            change
              Nat.succ x :: List.map Nat.succ (xs ++ l₂) =
                Nat.succ x :: (List.map Nat.succ xs ++ List.map Nat.succ l₂)
            exact congrArg (List.cons (Nat.succ x)) (ih l₂)
      have h_range :
          ∀ n : Nat,
            List.range (Nat.succ n) =
              0 :: List.map Nat.succ (List.range n) := by
        intro n
        induction n with
        | zero => rfl
        | succ m ih =>
            calc
              List.range (Nat.succ (Nat.succ m))
                  = List.range (Nat.succ m) ++ [Nat.succ m] :=
                    range_append (Nat.succ m)
              _ = (0 :: List.map Nat.succ (List.range m)) ++ [Nat.succ m] := by
                    rw [ih]
              _ = 0 :: (List.map Nat.succ (List.range m) ++ [Nat.succ m]) := rfl
              _ = 0 :: List.map Nat.succ (List.range m ++ [m]) := by
                    rw [map_succ_append]
                    rfl
              _ = 0 :: List.map Nat.succ (List.range (Nat.succ m)) := by
                    rw [range_append m]
      have h_range_width :
          List.range (Nat.succ width) =
            0 :: List.map Nat.succ (List.range width) :=
        h_range width
      have h_tail :
          List.map (C12.literalAt nVars seed clauseIdx)
              (List.map Nat.succ (List.range width)) =
            List.map
              (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
              (List.range width) := by
        induction List.range width with
        | nil => rfl
        | cons i is ih_tail =>
            rw [List.map_cons, List.map_cons, List.map_cons]
            rw [ih_tail]
      have h_map :
          List.map (C12.literalAt nVars seed clauseIdx)
              (List.range (Nat.succ width)) =
            C12.literalAt nVars seed clauseIdx 0 ::
              List.map
                (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
                (List.range width) := by
        rw [h_range_width]
        have h_cons :
            List.map (C12.literalAt nVars seed clauseIdx)
                (0 :: List.map Nat.succ (List.range width)) =
              C12.literalAt nVars seed clauseIdx 0 ::
                List.map (C12.literalAt nVars seed clauseIdx)
                  (List.map Nat.succ (List.range width)) := rfl
        rw [h_cons, h_tail]
      rw [h_map]
      have h_mem_tail :
          ∀ c ∈
            List.map
              (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
              (List.range width),
            IsClause c := by
        induction List.range width with
        | nil =>
            intro c hc
            cases hc
        | cons i is ih =>
            intro c hc
            cases hc with
            | head =>
                exact literalAt_isClause nVars seed clauseIdx (Nat.succ i)
            | tail _ hmem =>
                exact ih _ hmem
      exact foldl_or_preserves_isClause
        _ _
        (literalAt_isClause nVars seed clauseIdx 0)
        h_mem_tail


/-- Every structural clause is also a CNF formula. -/
theorem isClause_isCNF {c : Circuit} (h : IsClause c) : IsCNF c := by
  cases c with
  | input i =>
      exact True.intro
  | const b =>
      cases b with
      | false => exact True.intro
      | true => cases h
  | not c =>
      cases c with
      | input i => exact True.intro
      | const b => cases h
      | not c => cases h
      | and a b => cases h
      | or a b => cases h
  | and a b =>
      cases h
  | or a b =>
      exact h

/-- Every nonempty random clause is also a CNF formula. -/
theorem randomClause_isCNF
    (nVars seed clauseIdx width : Nat)
    (hwidth : 0 < width) :
    IsCNF (C12.randomClause nVars seed clauseIdx width) :=
  isClause_isCNF
    (randomClause_isClause nVars seed clauseIdx width hwidth)

/-- Folding conjunction over CNF formulas preserves CNF shape from a CNF accumulator. -/
theorem foldl_and_preserves_isCNF
    (xs : List Circuit) (acc : Circuit)
    (hacc : IsCNF acc)
    (hxs : ∀ c ∈ xs, IsCNF c) :
    IsCNF (xs.foldl (fun a c => .and a c) acc) := by
  induction xs generalizing acc with
  | nil =>
      exact hacc
  | cons x xs ih =>
      have hx : IsCNF x :=
        hxs x (List.Mem.head xs)
      have htail : ∀ c ∈ xs, IsCNF c := by
        intro c hc
        exact hxs c (List.Mem.tail x hc)
      exact ih (.and acc x) (IsCNF_and hacc hx) htail

/-- Every randomKCNF with positive clause count and width has CNF shape. -/
theorem randomKCNF_isCNF
    (nVars clauses width seed : Nat)
    (hclauses : 0 < clauses)
    (hwidth : 0 < width) :
    IsCNF (C12.randomKCNF nVars clauses width seed) := by
  unfold C12.randomKCNF
  cases clauses with
  | zero =>
      cases Nat.not_lt_zero 0 hclauses
  | succ clauses =>
      have h_range :
          ∀ n : Nat,
            List.range (Nat.succ n) =
              0 :: List.map Nat.succ (List.range n) := by
        intro n
        induction n with
        | zero => rfl
        | succ m ih =>
            have loop_append_single :
                ∀ (k : Nat) (acc : List Nat) (b : Nat),
                  List.range.loop k (acc ++ [b]) =
                    List.range.loop k acc ++ [b] := by
              intro k
              induction k with
              | zero =>
                  intro acc b
                  rfl
              | succ k ihk =>
                  intro acc b
                  calc
                    List.range.loop (Nat.succ k) (acc ++ [b])
                        = List.range.loop k (k :: (acc ++ [b])) := rfl
                    _ = List.range.loop k ((k :: acc) ++ [b]) := rfl
                    _ = List.range.loop k (k :: acc) ++ [b] := ihk (k :: acc) b
                    _ = List.range.loop (Nat.succ k) acc ++ [b] := rfl
            have range_append :
                ∀ k : Nat,
                  List.range (Nat.succ k) = List.range k ++ [k] := by
              intro k
              calc
                List.range (Nat.succ k)
                    = List.range.loop (Nat.succ k) [] := rfl
                _ = List.range.loop k [k] := rfl
                _ = List.range.loop k ([] ++ [k]) := rfl
                _ = List.range.loop k [] ++ [k] := loop_append_single k [] k
                _ = List.range k ++ [k] := rfl
            have map_succ_append :
                ∀ (l₁ l₂ : List Nat),
                  List.map Nat.succ (l₁ ++ l₂) =
                    List.map Nat.succ l₁ ++ List.map Nat.succ l₂ := by
              intro l₁
              induction l₁ with
              | nil =>
                  intro l₂
                  rfl
              | cons x xs ihxs =>
                  intro l₂
                  change
                    Nat.succ x :: List.map Nat.succ (xs ++ l₂) =
                      Nat.succ x ::
                        (List.map Nat.succ xs ++ List.map Nat.succ l₂)
                  exact congrArg (List.cons (Nat.succ x)) (ihxs l₂)
            calc
              List.range (Nat.succ (Nat.succ m))
                  = List.range (Nat.succ m) ++ [Nat.succ m] :=
                    range_append (Nat.succ m)
              _ = (0 :: List.map Nat.succ (List.range m)) ++ [Nat.succ m] := by
                    rw [ih]
              _ = 0 :: (List.map Nat.succ (List.range m) ++ [Nat.succ m]) := rfl
              _ = 0 :: List.map Nat.succ (List.range m ++ [m]) := by
                    rw [map_succ_append]
                    rfl
              _ = 0 :: List.map Nat.succ (List.range (Nat.succ m)) := by
                    rw [range_append m]
      have h_range_clauses :
          List.range (Nat.succ clauses) =
            0 :: List.map Nat.succ (List.range clauses) :=
        h_range clauses
      rw [h_range_clauses]
      have h_tail :
          List.map
              (fun c => C12.randomClause nVars seed c width)
              (List.map Nat.succ (List.range clauses)) =
            List.map
              (fun c => C12.randomClause nVars seed (Nat.succ c) width)
              (List.range clauses) := by
        induction List.range clauses with
        | nil => rfl
        | cons i is ih_tail =>
            rw [List.map_cons, List.map_cons, List.map_cons]
            rw [ih_tail]
      have h_cons :
          List.map
              (fun c => C12.randomClause nVars seed c width)
              (0 :: List.map Nat.succ (List.range clauses)) =
            C12.randomClause nVars seed 0 width ::
              List.map
                (fun c => C12.randomClause nVars seed (Nat.succ c) width)
                (List.range clauses) := by
        rw [List.map_cons, h_tail]
      rw [h_cons]
      have h_mem_tail :
          ∀ c ∈
            List.map
              (fun i => C12.randomClause nVars seed (Nat.succ i) width)
              (List.range clauses),
            IsCNF c := by
        induction List.range clauses with
        | nil =>
            intro c hc
            cases hc
        | cons i is ih =>
            intro c hc
            cases hc with
            | head =>
                exact randomClause_isCNF nVars seed (Nat.succ i) width hwidth
            | tail _ hmem =>
                exact ih _ hmem
      exact foldl_and_preserves_isCNF
        _ _
        (randomClause_isCNF nVars seed 0 width hwidth)
        h_mem_tail


/-- Canonical prefix serialization of the existing Circuit AST.
    This introduces no parallel CNF syntax: CNF remains the predicate IsCNF on Circuit. -/
def renderCNF : Circuit → String
  | .input i => "v(" ++ toString i ++ ")"
  | .const true => "T"
  | .const false => "F"
  | .not c => "n(" ++ renderCNF c ++ ")"
  | .and a b => "a(" ++ renderCNF a ++ "," ++ renderCNF b ++ ")"
  | .or a b => "o(" ++ renderCNF a ++ "," ++ renderCNF b ++ ")"


/-- Strings generated by the frozen prefix grammar used by renderCNF.
    This is a recognition predicate only; Circuit remains the canonical syntax tree. -/
inductive WellFormedCNFString : String → Prop where
  | input (i : Nat) : WellFormedCNFString ("v(" ++ toString i ++ ")")
  | trueConst : WellFormedCNFString "T"
  | falseConst : WellFormedCNFString "F"
  | not {s : String} (hs : WellFormedCNFString s) :
      WellFormedCNFString ("n(" ++ s ++ ")")
  | and {s₁ s₂ : String}
      (h₁ : WellFormedCNFString s₁) (h₂ : WellFormedCNFString s₂) :
      WellFormedCNFString ("a(" ++ s₁ ++ "," ++ s₂ ++ ")")
  | or {s₁ s₂ : String}
      (h₁ : WellFormedCNFString s₁) (h₂ : WellFormedCNFString s₂) :
      WellFormedCNFString ("o(" ++ s₁ ++ "," ++ s₂ ++ ")")

/-- Every serialization produced by the frozen renderer belongs to its grammar. -/
theorem wellFormed_of_render (φ : Circuit) :
    WellFormedCNFString (renderCNF φ) := by
  induction φ with
  | input i => exact WellFormedCNFString.input i
  | const b =>
      cases b with
      | false => exact WellFormedCNFString.falseConst
      | true => exact WellFormedCNFString.trueConst
  | not c ih => exact WellFormedCNFString.not ih
  | and a b iha ihb => exact WellFormedCNFString.and iha ihb
  | or a b iha ihb => exact WellFormedCNFString.or iha ihb


/-- Local decimal decoder. Kept structural so the parser core has no
    dependency on the library Char digit-classification/conversion path. -/
def charToDigit? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

/-- Parse a decimal numeral, returning the value and unconsumed characters.
    The boolean records whether at least one decimal digit was consumed. -/
def parseNatChars : List Char → Nat → Bool → Option (Nat × List Char)
  | [], acc, seen => if seen then some (acc, []) else none
  | c :: cs, acc, seen =>
      match charToDigit? c with
      | some d => parseNatChars cs (10 * acc + d) true
      | none => if seen then some (acc, c :: cs) else none

/-- Fuelled parser for the frozen renderCNF prefix language. -/
def parseCircuitChars : Nat → List Char → Option (Circuit × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
      match cs with
      | 'T' :: rest => some (.const true, rest)
      | 'F' :: rest => some (.const false, rest)
      | 'v' :: '(' :: rest =>
          match parseNatChars rest 0 false with
          | some (i, ')' :: tail) => some (.input i, tail)
          | _ => none
      | 'n' :: '(' :: rest =>
          match parseCircuitChars fuel rest with
          | some (c, ')' :: tail) => some (.not c, tail)
          | _ => none
      | 'a' :: '(' :: rest =>
          match parseCircuitChars fuel rest with
          | some (a, ',' :: rest') =>
              match parseCircuitChars fuel rest' with
              | some (b, ')' :: tail) => some (.and a b, tail)
              | _ => none
          | _ => none
      | 'o' :: '(' :: rest =>
          match parseCircuitChars fuel rest with
          | some (a, ',' :: rest') =>
              match parseCircuitChars fuel rest' with
              | some (b, ')' :: tail) => some (.or a b, tail)
              | _ => none
          | _ => none
      | _ => none

/-- Syntactic parser for the frozen renderCNF language.
    It parses Circuit syntax only; CNF validity is a separate predicate/check. -/
def parseCNF (s : String) : Option Circuit :=
  match parseCircuitChars (s.length + 1) s.toList with
  | some (c, []) => some c
  | _ => none


/-- Computable recognizer for the already-frozen structural CNF predicate. -/
def isClauseBool : Circuit → Bool
  | .const false => true
  | .input _ => true
  | .not (.input _) => true
  | .or a b => Bool.and (isClauseBool a) (isClauseBool b)
  | _ => false

def isCNFBool : Circuit → Bool
  | .const _ => true
  | .input _ => true
  | .not (.input _) => true
  | .or a b => Bool.and (isClauseBool a) (isClauseBool b)
  | .and a b => Bool.and (isCNFBool a) (isCNFBool b)
  | _ => false

theorem bool_and_eq_true_iff (x y : Bool) :
    Bool.and x y = true ↔ x = true ∧ y = true := by
  cases x <;> cases y
  · constructor
    · intro h; cases h
    · intro h; cases h.1
  · constructor
    · intro h; cases h
    · intro h; cases h.1
  · constructor
    · intro h; cases h
    · intro h; cases h.2
  · constructor
    · intro h; exact ⟨rfl, rfl⟩
    · intro h; rfl

theorem bool_and_decide_eq_true_iff (x y : Bool) :
    x && decide (y = true) = true ↔ x = true ∧ y = true := by
  cases x <;> cases y
  · constructor
    · intro h; cases h
    · intro h; cases h.1
  · constructor
    · intro h; cases h
    · intro h; cases h.1
  · constructor
    · intro h; cases h
    · intro h; cases h.2
  · constructor
    · intro h; exact ⟨rfl, rfl⟩
    · intro h; rfl

theorem isClauseBool_eq_true_iff (c : Circuit) :
    isClauseBool c = true ↔ IsClause c := by
  induction c with
  | input i =>
      constructor <;> intro h
      · exact True.intro
      · rfl
  | const b =>
      cases b with
      | false =>
          constructor <;> intro h
          · exact True.intro
          · rfl
      | true =>
          constructor <;> intro h
          · cases h
          · cases h
  | not c =>
      cases c with
      | input i =>
          constructor <;> intro h
          · exact True.intro
          · rfl
      | const b =>
          constructor <;> intro h
          · cases h
          · cases h
      | not c =>
          constructor <;> intro h
          · cases h
          · cases h
      | and a b =>
          constructor <;> intro h
          · cases h
          · cases h
      | or a b =>
          constructor <;> intro h
          · cases h
          · cases h
  | and a b iha ihb =>
      constructor <;> intro h
      · cases h
      · cases h
  | or a b iha ihb =>
      constructor
      · intro h
        have hab := (bool_and_eq_true_iff (isClauseBool a) (isClauseBool b)).mp h
        exact ⟨iha.mp hab.1, ihb.mp hab.2⟩
      · intro h
        exact (bool_and_eq_true_iff (isClauseBool a) (isClauseBool b)).mpr
          ⟨iha.mpr h.1, ihb.mpr h.2⟩

theorem isCNFBool_eq_true_iff (c : Circuit) :
    isCNFBool c = true ↔ IsCNF c := by
  induction c with
  | input i =>
      constructor <;> intro h
      · exact True.intro
      · rfl
  | const b =>
      cases b <;> constructor <;> intro h
      · exact True.intro
      · rfl
      · exact True.intro
      · rfl
  | not c =>
      cases c with
      | input i =>
          constructor <;> intro h
          · exact True.intro
          · rfl
      | const b =>
          constructor <;> intro h
          · cases h
          · cases h
      | not c =>
          constructor <;> intro h
          · cases h
          · cases h
      | and a b =>
          constructor <;> intro h
          · cases h
          · cases h
      | or a b =>
          constructor <;> intro h
          · cases h
          · cases h
  | and a b iha ihb =>
      constructor
      · intro h
        have hab := (bool_and_eq_true_iff (isCNFBool a) (isCNFBool b)).mp h
        exact ⟨iha.mp hab.1, ihb.mp hab.2⟩
      · intro h
        exact (bool_and_eq_true_iff (isCNFBool a) (isCNFBool b)).mpr
          ⟨iha.mpr h.1, ihb.mpr h.2⟩
  | or a b iha ihb =>
      constructor
      · intro h
        have hab := (bool_and_eq_true_iff (isClauseBool a) (isClauseBool b)).mp h
        exact ⟨
          (isClauseBool_eq_true_iff a).mp hab.1,
          (isClauseBool_eq_true_iff b).mp hab.2
        ⟩
      · intro h
        exact (bool_and_eq_true_iff (isClauseBool a) (isClauseBool b)).mpr
          ⟨
            (isClauseBool_eq_true_iff a).mpr h.1,
            (isClauseBool_eq_true_iff b).mpr h.2
          ⟩

end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalCircuitBits.lean BLOB 95db8597b479638fc0c035e951054d3043782272 -/
import MCore.Real.CanonicalSATBoundary

namespace MCore
namespace Real
namespace CanonicalCircuitBits

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary

def encodeNat : Nat → BitString
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def decodeNat : BitString → Option (Nat × BitString)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← decodeNat rest
      some (n + 1, tail)

theorem decodeNat_encodeNat_append
    (n : Nat) (tail : BitString) :
    decodeNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, decodeNat, ih]

/-- Fixed three-bit tags followed by recursively encoded payloads. -/
def encodeCircuit : Circuit → BitString
  | .input i => [false, false, false] ++ encodeNat i
  | .const false => [false, false, true]
  | .const true => [false, true, false]
  | .not c => [false, true, true] ++ encodeCircuit c
  | .and a b =>
      [true, false, false] ++ encodeCircuit a ++ encodeCircuit b
  | .or a b =>
      [true, false, true] ++ encodeCircuit a ++ encodeCircuit b

def decodeCircuitCore :
    Nat → BitString → Option (Circuit × BitString)
  | 0, _ => none
  | fuel + 1, bits =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (.input i, tail)
          | none => none
      | false :: false :: true :: rest =>
          some (.const false, rest)
      | false :: true :: false :: rest =>
          some (.const true, rest)
      | false :: true :: true :: rest =>
          match decodeCircuitCore fuel rest with
          | some (c, tail) => some (.not c, tail)
          | none => none
      | true :: false :: false :: rest =>
          match decodeCircuitCore fuel rest with
          | some (a, rest') =>
              match decodeCircuitCore fuel rest' with
              | some (b, tail) => some (.and a b, tail)
              | none => none
          | none => none
      | true :: false :: true :: rest =>
          match decodeCircuitCore fuel rest with
          | some (a, rest') =>
              match decodeCircuitCore fuel rest' with
              | some (b, tail) => some (.or a b, tail)
              | none => none
          | none => none
      | _ => none

theorem size_le_encodeCircuit_length
    (c : Circuit) :
    CircuitK1.size c ≤ (encodeCircuit c).length := by
  induction c with
  | input i =>
      simp [CircuitK1.size, encodeCircuit, encodeNat]
  | const b =>
      cases b <;> simp [CircuitK1.size, encodeCircuit]
  | not c ih =>
      simp [CircuitK1.size, encodeCircuit]
      omega
  | and a b iha ihb =>
      simp [CircuitK1.size, encodeCircuit]
      omega
  | or a b iha ihb =>
      simp [CircuitK1.size, encodeCircuit]
      omega

theorem decodeCircuitCore_encode_append
    (c : Circuit)
    (tail : BitString)
    (fuel : Nat)
    (hFuel : CircuitK1.size c < fuel) :
    decodeCircuitCore fuel (encodeCircuit c ++ tail) =
      some (c, tail) := by
  induction c generalizing fuel tail with
  | input i =>
      cases fuel with
      | zero => omega
      | succ f =>
          simp [encodeCircuit, decodeCircuitCore,
            decodeNat_encodeNat_append]
  | const b =>
      cases fuel with
      | zero => omega
      | succ f =>
          cases b <;> simp [encodeCircuit, decodeCircuitCore]
  | not c ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hc : CircuitK1.size c < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, ih _ _ hc]
  | and a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, List.append_assoc,
            iha _ _ ha, ihb _ _ hb]
  | or a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, List.append_assoc,
            iha _ _ ha, ihb _ _ hb]

def decodeCircuit (bits : BitString) : Option Circuit :=
  match decodeCircuitCore (bits.length + 1) bits with
  | some (c, []) => some c
  | _ => none

theorem decodeCircuit_encode
    (c : Circuit) :
    decodeCircuit (encodeCircuit c) = some c := by
  have hFuel :
      CircuitK1.size c < (encodeCircuit c).length + 1 :=
    Nat.lt_succ_of_le (size_le_encodeCircuit_length c)
  have hCore :=
    decodeCircuitCore_encode_append
      c ([] : BitString) ((encodeCircuit c).length + 1) hFuel
  have hCore' :
      decodeCircuitCore ((encodeCircuit c).length + 1) (encodeCircuit c) =
        some (c, []) := by
    simpa using hCore
  simp [decodeCircuit, hCore']

def circuitBitEncoding : CircuitBitEncoding :=
  { encode := encodeCircuit
    decode := decodeCircuit
    decode_encode := decodeCircuit_encode }

theorem canonical_sat_encoding_closed :
    SATEncodingGap := by
  exact ⟨circuitBitEncoding⟩

theorem encoded_sat_equivalence
    (φ : Circuit) :
    SATBits circuitBitEncoding (encodeCircuit φ) ↔ SATLanguage φ :=
  encoded_sat_iff circuitBitEncoding φ

#print axioms MCore.Real.CanonicalCircuitBits.decodeNat_encodeNat_append
#print axioms MCore.Real.CanonicalCircuitBits.size_le_encodeCircuit_length
#print axioms MCore.Real.CanonicalCircuitBits.decodeCircuitCore_encode_append
#print axioms MCore.Real.CanonicalCircuitBits.decodeCircuit_encode
#print axioms MCore.Real.CanonicalCircuitBits.canonical_sat_encoding_closed
#print axioms MCore.Real.CanonicalCircuitBits.encoded_sat_equivalence

end CanonicalCircuitBits
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalComplexityBridge.lean BLOB 0b44ea4c066781a6537a5a600e31e2384a47f8a4 -/
import MCore.K9
import MCore.Real.CanonicalPSubsetNP
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace CanonicalComplexityBridge

open CanonicalFinalProof
open CanonicalPSubsetNP
open FailProofAllGaps

def canonicalInterface : ClassicalComplexityInterface BitLanguage :=
  { inP := InP
    inNP := InNP
    p_subset_np := inP_subset_inNP }

theorem canonical_interface_p_match
    (L : BitLanguage) :
    canonicalInterface.inP L ↔ InP L :=
  Iff.rfl

theorem canonical_interface_np_match
    (L : BitLanguage) :
    canonicalInterface.inNP L ↔ InNP L :=
  Iff.rfl

def canonicalExternalMatch :
    ExternalModelMatch canonicalInterface.inP canonicalInterface.inNP :=
  { p_match := fun _ => Iff.rfl
    np_match := fun _ => Iff.rfl }

theorem canonical_failure_witness_separates_legacy_interface
    {L : BitLanguage}
    (hNP : canonicalInterface.inNP L)
    (hFail : UniversalFailure L) :
    ¬ (∀ X : BitLanguage,
      canonicalInterface.inP X ↔ canonicalInterface.inNP X) := by
  intro hEq
  have hP : InP L := (hEq L).mpr hNP
  exact (universal_failure_implies_not_in_p hFail) hP

#print axioms MCore.Real.CanonicalComplexityBridge.canonical_interface_p_match
#print axioms MCore.Real.CanonicalComplexityBridge.canonical_interface_np_match
#print axioms MCore.Real.CanonicalComplexityBridge.canonical_failure_witness_separates_legacy_interface

end CanonicalComplexityBridge
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalFinalProof.lean BLOB 247f0e5cef8314c3a3cf3fd6bab87f48eb867c43 -/
import MCore.Real.Model

namespace MCore
namespace Real
namespace CanonicalFinalProof

abbrev BitString := List Bool
abbrev BitLanguage := BitString → Prop

/-- Canonical tape encoding. none is the blank/end marker, so the empty input
    is distinct from an input beginning with false. -/
def inputTape : BitString → Tape (Option Bool)
  | [] =>
      { left := []
        head := none
        right := [] }
  | b :: bs =>
      { left := []
        head := some b
        right := bs.map some }

def initialTMConfig
    {stateCount : Nat}
    (machine : TM (Fin (stateCount + 1)) (Option Bool))
    (x : BitString) :
    Configuration (Fin (stateCount + 1)) (Option Bool) :=
  { state := machine.initial
    tape := inputTape x }

def initialNTMConfig
    {stateCount : Nat}
    (machine : NTM (Fin (stateCount + 1)) (Option Bool))
    (x : BitString) :
    Configuration (Fin (stateCount + 1)) (Option Bool) :=
  { state := machine.initial
    tape := inputTape x }

/-- Polynomial bound with constants fixed per machine. -/
def PolynomialTimeBound (T : TimeBound) : Prop :=
  ∃ coefficient exponent : Nat, ∀ n : Nat,
    T n ≤ coefficient * (n + 1) ^ exponent

/-- Hardened deterministic candidate:
    finite control, fixed alphabet, canonical input, blank = none,
    and no arbitrary input encoder field. -/
structure PolyDTMCandidate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def PolyDTMCandidate.CorrectAt
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialTMConfig candidate.machine x
  candidate.machine.HaltsWithin (candidate.timeBound x.length) config ∧
    (candidate.accepting
        (candidate.machine.run (candidate.timeBound x.length) config).state = true
      ↔ language x)

structure PolyDTMRealization (language : BitLanguage) where
  candidate : PolyDTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt language x

/-- Hardened nondeterministic candidate with the same finite/canonical model. -/
structure PolyNTMCandidate where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def PolyNTMCandidate.CorrectAt
    (candidate : PolyNTMCandidate)
    (language : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialNTMConfig candidate.machine x
  candidate.machine.HaltsWithin (candidate.timeBound x.length) config ∧
    (candidate.machine.AcceptsWithin (candidate.timeBound x.length) config
      ↔ language x)

structure PolyNTMRealization (language : BitLanguage) where
  candidate : PolyNTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt language x

def InP (language : BitLanguage) : Prop :=
  Nonempty (PolyDTMRealization language)

def InNP (language : BitLanguage) : Prop :=
  Nonempty (PolyNTMRealization language)

def PneqNP : Prop :=
  ¬ ∀ language : BitLanguage, InP language ↔ InNP language

/-- Operational fail proof for one fixed language:
    every finite-control deterministic polynomial-time candidate has a concrete
    bitstring input on which it fails. -/
def UniversalFailure (language : BitLanguage) : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString, ¬ candidate.CorrectAt language x

theorem universal_failure_implies_not_in_p
    {language : BitLanguage}
    (hFail : UniversalFailure language) :
    ¬ InP language := by
  intro hP
  rcases hP with ⟨realization⟩
  rcases hFail realization.candidate with ⟨x, hBad⟩
  exact hBad (realization.decides x)

theorem not_in_p_implies_universal_failure
    {language : BitLanguage}
    (hNotP : ¬ InP language) :
    UniversalFailure language := by
  intro candidate
  apply Classical.byContradiction
  intro hNoFailure
  apply hNotP
  refine ⟨{ candidate := candidate, decides := ?_ }⟩
  intro x
  apply Classical.byContradiction
  intro hBad
  exact hNoFailure ⟨x, hBad⟩

theorem universal_failure_iff_not_in_p
    {language : BitLanguage} :
    UniversalFailure language ↔ ¬ InP language := by
  constructor
  · exact universal_failure_implies_not_in_p
  · exact not_in_p_implies_universal_failure

/-- One genuine NP language plus a universal deterministic fail proof is exactly
    enough to separate the two machine classes. -/
theorem target_failure_implies_p_ne_np
    {language : BitLanguage}
    (hNP : InNP language)
    (hFail : UniversalFailure language) :
    PneqNP := by
  intro hEq
  have hP : InP language :=
    (hEq language).mpr hNP
  exact (universal_failure_implies_not_in_p hFail) hP

/-- Hardened endpoint payload. The target language is explicit rather than
    assumed to be SAT until a certified bitstring SAT encoding is supplied. -/
structure SeparationCertificate where
  target : BitLanguage
  target_in_np : InNP target
  fail_proof : UniversalFailure target

theorem separation_certificate_closes
    (cert : SeparationCertificate) :
    PneqNP :=
  target_failure_implies_p_ne_np cert.target_in_np cert.fail_proof

#print axioms MCore.Real.CanonicalFinalProof.universal_failure_implies_not_in_p
#print axioms MCore.Real.CanonicalFinalProof.not_in_p_implies_universal_failure
#print axioms MCore.Real.CanonicalFinalProof.universal_failure_iff_not_in_p
#print axioms MCore.Real.CanonicalFinalProof.target_failure_implies_p_ne_np
#print axioms MCore.Real.CanonicalFinalProof.separation_certificate_closes

end CanonicalFinalProof
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalPSubsetNP.lean BLOB 5ba695ae41be2b0848a518732bcadbc7649f6cd2 -/
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalPSubsetNP

open CanonicalFinalProof

def toNTM
    (candidate : PolyDTMCandidate) :
    NTM (Fin (candidate.stateCount + 1)) (Option Bool) :=
  { initial := candidate.machine.initial
    blank := candidate.machine.blank
    transition := fun q symbol => [candidate.machine.transition q symbol]
    accepting := fun q =>
      Bool.and (candidate.machine.halting q) (candidate.accepting q)
    rejecting := fun q =>
      Bool.and (candidate.machine.halting q) (!(candidate.accepting q)) }

theorem accept_or_reject_eq_halting
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1)) :
    ((toNTM candidate).accepting q || (toNTM candidate).rejecting q) =
      candidate.machine.halting q := by
  cases h : candidate.machine.halting q <;>
    cases a : candidate.accepting q <;>
    simp [toNTM, h, a]

theorem successors_toNTM
    (candidate : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (toNTM candidate).successors config =
      [candidate.machine.step config] := by
  rfl

theorem tm_run_of_halted
    (candidate : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool))
    (h : candidate.machine.halting config.state = true) :
    ∀ fuel : Nat, candidate.machine.run fuel config = config := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ n =>
      simp [TM.run, h]

theorem runBranches_to_tm_run
    (candidate : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (toNTM candidate).runBranches fuel [config] =
      [candidate.machine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ n ih =>
      by_cases h : candidate.machine.halting config.state = true
      · have hstop :
          ((toNTM candidate).accepting config.state ||
            (toNTM candidate).rejecting config.state) = true := by
          rw [accept_or_reject_eq_halting]
          exact h
        have hHalted :
            [config].filter (fun c =>
              (toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state) = [config] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((toNTM candidate).accepting config.state ||
                (toNTM candidate).rejecting config.state) = false := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state)) = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (toNTM candidate).runBranches (n + 1) [config]
              = (toNTM candidate).runBranches n [config] := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = [candidate.machine.run n config] := ih config
          _ = [config] := by
                rw [tm_run_of_halted candidate config h n]
          _ = [candidate.machine.run (n + 1) config] := by
                simp [TM.run, h]
      · have hFalse : candidate.machine.halting config.state = false := by
          cases hval : candidate.machine.halting config.state <;> simp_all
        have hstop :
          ((toNTM candidate).accepting config.state ||
            (toNTM candidate).rejecting config.state) = false := by
          rw [accept_or_reject_eq_halting]
          exact hFalse
        have hHalted :
            [config].filter (fun c =>
              (toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state) = [] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((toNTM candidate).accepting config.state ||
                (toNTM candidate).rejecting config.state) = true := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state)) = [config] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (toNTM candidate).runBranches (n + 1) [config]
              = (toNTM candidate).runBranches n
                  ((toNTM candidate).successors config) := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = (toNTM candidate).runBranches n
                  [candidate.machine.step config] := by
                rw [successors_toNTM]
          _ = [candidate.machine.run n (candidate.machine.step config)] :=
                ih (candidate.machine.step config)
          _ = [candidate.machine.run (n + 1) config] := by
                simp [TM.run, h]

def toNTMCandidate
    (candidate : PolyDTMCandidate) :
    PolyNTMCandidate :=
  { stateCount := candidate.stateCount
    machine := toNTM candidate
    blank_none := candidate.blank_none
    timeBound := candidate.timeBound
    time_poly := candidate.time_poly }

theorem correctAt_to_ntm
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString)
    (hCorrect : candidate.CorrectAt language x) :
    (toNTMCandidate candidate).CorrectAt language x := by
  rcases hCorrect with ⟨hHalt, hAccept⟩
  have hHaltEq :
      candidate.machine.halting
        (candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)).state = true :=
    hHalt
  constructor
  · intro reached hMem
    have hRuns :=
      runBranches_to_tm_run candidate
        (candidate.timeBound x.length)
        (initialTMConfig candidate.machine x)
    change
      reached ∈
        (toNTM candidate).runBranches
          (candidate.timeBound x.length)
          [initialTMConfig candidate.machine x] at hMem
    rw [hRuns] at hMem
    have hEq :
        reached =
          candidate.machine.run
            (candidate.timeBound x.length)
            (initialTMConfig candidate.machine x) := by
      simpa using hMem
    subst reached
    by_cases ha :
        candidate.accepting
          (candidate.machine.run
            (candidate.timeBound x.length)
            (initialTMConfig candidate.machine x)).state = true
    · left
      simp [toNTMCandidate, toNTM, hHaltEq, ha]
    · right
      have haFalse :
          candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state = false := by
        cases hval :
          candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state <;> simp_all
      simp [toNTMCandidate, toNTM, hHaltEq, haFalse]
  · constructor
    · intro hNAcc
      rcases hNAcc with ⟨reached, hMem, hAcc⟩
      have hRuns :=
        runBranches_to_tm_run candidate
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)
      change
        reached ∈
          (toNTM candidate).runBranches
            (candidate.timeBound x.length)
            [initialTMConfig candidate.machine x] at hMem
      rw [hRuns] at hMem
      have hEq :
          reached =
            candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x) := by
        simpa using hMem
      subst reached
      have hCandidateAccept :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = true := by
        simpa [toNTMCandidate, toNTM, hHaltEq] using hAcc
      exact hAccept.mp hCandidateAccept
    · intro hLanguage
      have hCandidateAccept :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = true :=
        hAccept.mpr hLanguage
      refine ⟨
        candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x),
        ?_, ?_⟩
      · change
          candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x) ∈
            (toNTM candidate).runBranches
              (candidate.timeBound x.length)
              [initialTMConfig candidate.machine x]
        rw [runBranches_to_tm_run]
        simp
      · simp [toNTMCandidate, toNTM, hHaltEq, hCandidateAccept]

def realization_to_ntm
    {language : BitLanguage}
    (R : PolyDTMRealization language) :
    PolyNTMRealization language :=
  { candidate := toNTMCandidate R.candidate
    decides := fun x => correctAt_to_ntm R.candidate language x (R.decides x) }

theorem inP_subset_inNP
    (language : BitLanguage) :
    InP language → InNP language := by
  rintro ⟨R⟩
  exact ⟨realization_to_ntm R⟩

#print axioms MCore.Real.CanonicalPSubsetNP.accept_or_reject_eq_halting
#print axioms MCore.Real.CanonicalPSubsetNP.runBranches_to_tm_run
#print axioms MCore.Real.CanonicalPSubsetNP.correctAt_to_ntm
#print axioms MCore.Real.CanonicalPSubsetNP.inP_subset_inNP

end CanonicalPSubsetNP
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATBoundary.lean BLOB 10df41e32aaa8b08f650b8d76b8a85db0ef7afc4 -/
import MCore.Real.CNFStructure
import MCore.Real.Semantics
import MCore.Real.SATMachine
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace CanonicalSATBoundary

open CircuitK1
open CanonicalFinalProof
open FailProofAllGaps

/-- A semantics-preserving bitstring boundary for the existing Circuit AST.
    Circuit remains the syntax; this does not introduce a second SAT syntax. -/
structure CircuitBitEncoding where
  encode : Circuit → BitString
  decode : BitString → Option Circuit
  decode_encode : ∀ φ : Circuit, decode (encode φ) = some φ

/-- SAT language induced on bitstrings by one exact Circuit encoding. -/
def SATBits (E : CircuitBitEncoding) : BitLanguage :=
  fun x =>
    ∃ φ : Circuit,
      E.decode x = some φ ∧ SATLanguage φ

theorem encoded_sat_iff
    (E : CircuitBitEncoding)
    (φ : Circuit) :
    SATBits E (E.encode φ) ↔ SATLanguage φ := by
  constructor
  · rintro ⟨ψ, hdecode, hsat⟩
    rw [E.decode_encode φ] at hdecode
    have hEq : φ = ψ := Option.some.inj hdecode
    simpa [hEq] using hsat
  · intro hsat
    exact ⟨φ, E.decode_encode φ, hsat⟩

/-- G1a: an actual exact bit encoding of the existing Circuit syntax. -/
def SATEncodingGap : Prop :=
  Nonempty CircuitBitEncoding

/-- G1b: after fixing an encoding, the induced SAT bit-language has a concrete
    polynomial-time nondeterministic machine in the hardened model. -/
def SATInNPGap (E : CircuitBitEncoding) : Prop :=
  InNP (SATBits E)

/-- G2: the genuine lower-bound/fail-proof object for the same SAT language. -/
def SATFailGap (E : CircuitBitEncoding) : Prop :=
  Nonempty (FailureGenerator (SATBits E))

/-- Full internal SAT closure. -/
structure SATInternalClosure where
  encoding : CircuitBitEncoding
  sat_in_np : SATInNPGap encoding
  fail_generator : FailureGenerator (SATBits encoding)

theorem sat_internal_closure_implies_p_ne_np
    (C : SATInternalClosure) :
    PneqNP := by
  have hFail : UniversalFailure (SATBits C.encoding) :=
    failure_generator_implies_universal_failure C.fail_generator
  exact target_failure_implies_p_ne_np C.sat_in_np hFail

/-- Full external closure adds only the model-equivalence adapter. -/
structure SATExternalClosure
    (officialP officialNP : BitLanguage → Prop)
    extends SATInternalClosure where
  model_match : ExternalModelMatch officialP officialNP

theorem sat_external_closure_implies_official_separation
    {officialP officialNP : BitLanguage → Prop}
    (C : SATExternalClosure officialP officialNP) :
    OfficialPneqNP officialP officialNP := by
  have hInternal : PneqNP :=
    sat_internal_closure_implies_p_ne_np C.toSATInternalClosure
  exact internal_separation_transfers C.model_match hInternal

#print axioms MCore.Real.CanonicalSATBoundary.encoded_sat_iff
#print axioms MCore.Real.CanonicalSATBoundary.sat_internal_closure_implies_p_ne_np
#print axioms MCore.Real.CanonicalSATBoundary.sat_external_closure_implies_official_separation

end CanonicalSATBoundary
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATFrameAttack.lean BLOB ec413cf6554179a25eb3b3d5d4d99b1c4fd13842 -/
import MCore.Real.CanonicalSATNatParserAttack

namespace MCore
namespace Real
namespace CanonicalSATFrameAttack

open CanonicalFinalProof

/-- Recursive parser continuation frames needed by prefix Circuit parsing.
    Binary constructors need two phases: waiting for the left child and then
    waiting for the right child. -/
inductive Frame where
  | neg
  | andLeft
  | andRight
  | orLeft
  | orRight
  deriving DecidableEq, Repr

/-- Fixed-width binary representation of parser frames. -/
def encodeFrame : Frame → List Bool
  | .neg      => [false, false, false]
  | .andLeft  => [false, false, true]
  | .andRight => [false, true, false]
  | .orLeft   => [false, true, true]
  | .orRight  => [true, false, false]

def decodeFrame : List Bool → Option Frame
  | [false, false, false] => some .neg
  | [false, false, true]  => some .andLeft
  | [false, true, false]  => some .andRight
  | [false, true, true]   => some .orLeft
  | [true, false, false]  => some .orRight
  | _ => none

@[simp] theorem decodeFrame_encodeFrame
    (f : Frame) :
    decodeFrame (encodeFrame f) = some f := by
  cases f <;> rfl

@[simp] theorem encodeFrame_length
    (f : Frame) :
    (encodeFrame f).length = 3 := by
  cases f <;> rfl

def encodeFrames : List Frame → List Bool
  | [] => []
  | f :: fs => encodeFrame f ++ encodeFrames fs

def decodeFrames : List Bool → Option (List Frame)
  | [] => some []
  | a :: b :: c :: rest => do
      let f ← decodeFrame [a,b,c]
      let fs ← decodeFrames rest
      some (f :: fs)
  | _ => none

theorem decodeFrames_encodeFrames
    (fs : List Frame) :
    decodeFrames (encodeFrames fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f <;>
        simp [encodeFrames, encodeFrame, decodeFrames, decodeFrame, ih]

theorem encodeFrames_length
    (fs : List Frame) :
    (encodeFrames fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [encodeFrames, encodeFrame_length, ih]
      omega

theorem encoded_stack_linear_space
    (fs : List Frame)
    (inputLength : Nat)
    (hDepth : fs.length ≤ inputLength) :
    (encodeFrames fs).length ≤ 3 * inputLength := by
  rw [encodeFrames_length]
  exact Nat.mul_le_mul_left 3 hDepth

/-- Functional push representation; the machine-level implementation is still
    required separately. -/
theorem encodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    encodeFrames (f :: fs) =
      encodeFrame f ++ encodeFrames fs := by
  rfl

/-- Functional pop round-trip after decoding a well-formed encoded stack. -/
theorem decodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    decodeFrames (encodeFrame f ++ encodeFrames fs) =
      some (f :: fs) := by
  simpa [encodeFrames] using decodeFrames_encodeFrames (f :: fs)

/-!
Fail-proof hardening of the frame-tape boundary.

The previous certificate carried only an arbitrary machine and a polynomial
bound.  That shape is trivially inhabitable and therefore cannot certify
frame push/pop semantics.  The hardened certificate below fixes an explicit
command protocol and requires the machine to halt and return the exact
canonical stack encoding.
-/

def pushCommand (f : Frame) (fs : List Frame) : BitString :=
  true :: (encodeFrame f ++ encodeFrames fs)

def popCommand (fs : List Frame) : BitString :=
  false :: encodeFrames fs

/-- Legacy under-specified shape, retained only for the fail-proof theorem. -/
structure LegacyFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

/-- The legacy gate is vacuous: a one-state halted machine with zero time
    bound inhabits it without implementing any stack operation. -/
theorem legacy_frame_gate_is_trivially_inhabited :
    Nonempty LegacyFrameTapeMachineCertificate := by
  let trivialMachine : TM (Fin 1) (Option Bool) :=
    { initial := 0
      blank := none
      transition := fun q symbol => (q, symbol, .stay)
      halting := fun _ => true }
  have hpoly : PolynomialTimeBound (fun _ => 0) := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp
  exact ⟨
    { stateCount := 0
      machine := trivialMachine
      timeBound := fun _ => 0
      time_poly := hpoly }⟩

/-- Read the finite Boolean word from the current head to the first blank.
    Explicit blanks after the semantic end are ignored, matching the intended
    infinite-blank tape semantics rather than raw list representation. -/
def readTapeCells : List (Option Bool) → BitString
  | [] => []
  | none :: _ => []
  | some b :: rest => b :: readTapeCells rest

/-- Boolean word represented from the current tape head. -/
def tapeWord (t : Tape (Option Bool)) : BitString :=
  match t.head with
  | none => []
  | some b => b :: readTapeCells t.right

/-- Canonical-head semantic representation: the machine has rewound to the
    left boundary and the visible word agrees with the requested bitstring. -/
def TapeRepresents (bits : BitString) (t : Tape (Option Bool)) : Prop :=
  t.left = [] ∧ tapeWord t = bits

@[simp] theorem readTapeCells_map_some
    (bits : BitString) :
    readTapeCells (bits.map some) = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      simp [readTapeCells, ih]

@[simp] theorem tapeWord_inputTape
    (bits : BitString) :
    tapeWord (inputTape bits) = bits := by
  cases bits <;> simp [tapeWord, inputTape, readTapeCells]

theorem inputTape_represents
    (bits : BitString) :
    TapeRepresents bits (inputTape bits) := by
  constructor
  · cases bits <;> rfl
  · exact tapeWord_inputTape bits

/-- Raw Tape equality is strictly stronger than represented-word equality:
    an explicit trailing blank changes the structure but not the word. -/
def trailingBlankTape : Tape (Option Bool) :=
  { left := [], head := some true, right := [none] }

theorem trailingBlankTape_represents :
    TapeRepresents [true] trailingBlankTape := by
  simp [TapeRepresents, trailingBlankTape, tapeWord, readTapeCells]

theorem trailingBlankTape_ne_inputTape :
    trailingBlankTape ≠ inputTape [true] := by
  simp [trailingBlankTape, inputTape]

/-- Hardened operational boundary.  Push is presented as
    1 || frame || stack and pop as 0 || stack.  Successful execution must
    normalize the final tape back to the canonical stack encoding. -/
structure FrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))

  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      (machine.run
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))).tape =
      inputTape (encodeFrames (f :: fs))

  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))

  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      (machine.run
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))).tape =
      inputTape (encodeFrames fs)

def FrameTapeOperationalGap : Prop :=
  Nonempty FrameTapeMachineCertificate

/-- Semantically hardened variant: exact represented output is required, while
    harmless explicit trailing blanks are quotient-like implementation detail. -/
structure SemanticFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))

  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresents
        (encodeFrames (f :: fs))
        (machine.run
          (timeBound (pushCommand f fs).length)
          (initialTMConfig machine (pushCommand f fs))).tape

  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))

  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresents
        (encodeFrames fs)
        (machine.run
          (timeBound (popCommand (f :: fs)).length)
          (initialTMConfig machine (popCommand (f :: fs)))).tape

def SemanticFrameTapeOperationalGap : Prop :=
  Nonempty SemanticFrameTapeMachineCertificate

def FrameTapeMachineCertificate.toSemantic
    (C : FrameTapeMachineCertificate) :
    SemanticFrameTapeMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly
    push_halts := C.push_halts
    push_correct := by
      intro f fs
      rw [C.push_correct f fs]
      exact inputTape_represents _
    pop_halts := C.pop_halts
    pop_correct := by
      intro f fs
      rw [C.pop_correct f fs]
      exact inputTape_represents _ }

theorem exact_frame_tape_implies_semantic
    (h : FrameTapeOperationalGap) :
    SemanticFrameTapeOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toSemantic⟩

#print axioms MCore.Real.CanonicalSATFrameAttack.trailingBlankTape_ne_inputTape
#print axioms MCore.Real.CanonicalSATFrameAttack.exact_frame_tape_implies_semantic

/-- The hardened frame-tape certificate is strong enough to discharge the
    earlier structural recursive-frame existence gate.  This does not create
    the missing machine; it wires a genuine future implementation into the
    existing parser chain without weakening its semantics. -/
def FrameTapeMachineCertificate.toRecursiveFrameMachineCertificate
    (C : FrameTapeMachineCertificate) :
    CanonicalSATNatParserAttack.RecursiveFrameMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem frame_tape_operational_closes_recursive_frame
    (h : FrameTapeOperationalGap) :
    CanonicalSATNatParserAttack.RecursiveFrameOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toRecursiveFrameMachineCertificate⟩

#print axioms MCore.Real.CanonicalSATFrameAttack.frame_tape_operational_closes_recursive_frame

#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrame_encodeFrame
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_encodeFrames
#print axioms MCore.Real.CanonicalSATFrameAttack.encodeFrames_length
#print axioms MCore.Real.CanonicalSATFrameAttack.encoded_stack_linear_space
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_push
#print axioms MCore.Real.CanonicalSATFrameAttack.legacy_frame_gate_is_trivially_inhabited

end CanonicalSATFrameAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATFrameMachineV2.lean BLOB 829e02aef78a7f49b7b09c4a66c95b513bd60c06 -/
import MCore.Real.CanonicalSATFrameAttack

namespace MCore
namespace Real
namespace CanonicalSATFrameMachineV2

open CanonicalFinalProof
open CanonicalSATFrameAttack

/-- Infinite-blank tape semantics: explicit blank cells to the left of the
current head are observationally irrelevant. This is the left-hand analogue
of `readTapeCells` ignoring trailing blanks on the right. -/
def LeftBlankPadding (t : Tape (Option Bool)) : Prop :=
  ∀ s ∈ t.left, s = none

def TapeRepresentsModuloBlankPadding
    (bits : BitString) (t : Tape (Option Bool)) : Prop :=
  LeftBlankPadding t ∧ tapeWord t = bits

def paddedInputTape (k : Nat) : BitString → Tape (Option Bool)
  | [] =>
      { left := List.replicate k none
        head := none
        right := [] }
  | b :: bs =>
      { left := List.replicate k none
        head := some b
        right := bs.map some }

theorem paddedInputTape_represents
    (k : Nat) (bits : BitString) :
    TapeRepresentsModuloBlankPadding bits (paddedInputTape k bits) := by
  cases bits <;>
    simp [TapeRepresentsModuloBlankPadding, LeftBlankPadding,
      paddedInputTape, tapeWord, readTapeCells]

/-- Five-state finite-control machine implementing the frame command protocol.
State 0 dispatches on the command bit. A push command erases one prefix cell
and halts. A pop command erases the command plus the three fixed-width frame
bits and halts at the first stack bit. -/
def frameCommandMachine : TM (Fin 5) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true => (4, none, .right)
        | some false => (1, none, .right)
        | none => (4, none, .stay)
      else if q = 1 then
        (2, none, .right)
      else if q = 2 then
        (3, none, .right)
      else if q = 3 then
        (4, none, .right)
      else
        (4, symbol, .stay)
    halting := fun q => q == 4 }

@[simp] theorem frameCommandMachine_halt4 :
    frameCommandMachine.halting (4 : Fin 5) = true := by rfl

@[simp] theorem frameCommandMachine_not_halt0 :
    frameCommandMachine.halting (0 : Fin 5) = false := by rfl

/-- Push is one semantic machine step; extra fuel is inert after the halting
state is reached. -/
theorem frameCommandMachine_run_push
    (f : Frame) (fs : List Frame) :
    frameCommandMachine.run 4
      (initialTMConfig frameCommandMachine (pushCommand f fs)) =
      { state := (4 : Fin 5)
        tape := paddedInputTape 1 (encodeFrames (f :: fs)) } := by
  cases f <;>
    simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
      pushCommand, encodeFrames, encodeFrame, inputTape,
      paddedInputTape, Tape.write, Tape.move]

/-- Pop erases exactly four protocol cells: command + one three-bit frame. -/
theorem frameCommandMachine_run_pop
    (f : Frame) (fs : List Frame) :
    frameCommandMachine.run 4
      (initialTMConfig frameCommandMachine (popCommand (f :: fs))) =
      { state := (4 : Fin 5)
        tape := paddedInputTape 4 (encodeFrames fs) } := by
  cases f <;>
  cases fs with
  | nil =>
      simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
        popCommand, encodeFrames, encodeFrame, inputTape,
        paddedInputTape, Tape.write, Tape.move]
  | cons g gs =>
      cases g <;>
        simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
          popCommand, encodeFrames, encodeFrame, inputTape,
          paddedInputTape, Tape.write, Tape.move]

def frameCommandTimeBound : TimeBound := fun _ => 4

theorem frameCommandTimeBound_poly :
    PolynomialTimeBound frameCommandTimeBound := by
  refine ⟨4, 0, ?_⟩
  intro n
  simp [frameCommandTimeBound]

structure BlankNormalizedFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))
  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresentsModuloBlankPadding
        (encodeFrames (f :: fs))
        (machine.run
          (timeBound (pushCommand f fs).length)
          (initialTMConfig machine (pushCommand f fs))).tape
  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))
  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresentsModuloBlankPadding
        (encodeFrames fs)
        (machine.run
          (timeBound (popCommand (f :: fs)).length)
          (initialTMConfig machine (popCommand (f :: fs)))).tape

def frameCommandMachine_certificate :
    BlankNormalizedFrameTapeMachineCertificate := by
  refine
    { stateCount := 4
      machine := frameCommandMachine
      blank_none := rfl
      timeBound := frameCommandTimeBound
      time_poly := frameCommandTimeBound_poly
      push_halts := ?_
      push_correct := ?_
      pop_halts := ?_
      pop_correct := ?_ }
  · intro f fs
    rw [TM.HaltsWithin]
    simp [frameCommandTimeBound, frameCommandMachine_run_push]
  · intro f fs
    rw [frameCommandTimeBound, frameCommandMachine_run_push]
    exact paddedInputTape_represents 1 _
  · intro f fs
    rw [TM.HaltsWithin]
    simp [frameCommandTimeBound, frameCommandMachine_run_pop]
  · intro f fs
    rw [frameCommandTimeBound, frameCommandMachine_run_pop]
    exact paddedInputTape_represents 4 _

def BlankNormalizedFrameTapeOperationalGap : Prop :=
  Nonempty BlankNormalizedFrameTapeMachineCertificate

theorem blank_normalized_frame_tape_operational_closed :
    BlankNormalizedFrameTapeOperationalGap :=
  ⟨frameCommandMachine_certificate⟩

#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_run_push
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_run_pop
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandTimeBound_poly
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_certificate
#print axioms MCore.Real.CanonicalSATFrameMachineV2.blank_normalized_frame_tape_operational_closed

end CanonicalSATFrameMachineV2
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATNTMAttack.lean BLOB aafdb20728f951879a4b8286b7e2557264bd8575 -/
import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace CanonicalSATNTMAttack

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATVerifier

/-- Canonical two-state tape scanner.
    State 0 scans right across input bits.
    State 1 is the halting state reached at the first blank. -/
def scanMachine : TM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | none => (1, none, .stay)
        | some b => (0, some b, .right)
      else
        (1, symbol, .stay)
    halting := fun q => q == 1 }

/-- Generalized canonical scanning configuration; the left list is the already
    visited tape prefix in the tape's native reversed-left convention. -/
def scanConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 2) (Option Bool) :=
  match bits with
  | [] =>
      { state := 0
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem scanConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (scanConfig left bits).state = (0 : Fin 2) := by
  cases bits <;> rfl

@[simp] theorem scanMachine_not_halted_at_zero :
    scanMachine.halting (0 : Fin 2) = false := by
  rfl

@[simp] theorem scanMachine_halted_at_one :
    scanMachine.halting (1 : Fin 2) = true := by
  rfl

theorem scan_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    scanMachine.step (scanConfig left (b :: bs)) =
      scanConfig (some b :: left) bs := by
  cases bs <;>
    simp [scanMachine, scanConfig, TM.step, Tape.write, Tape.move]

theorem scan_step_nil
    (left : List (Option Bool)) :
    scanMachine.step (scanConfig left []) =
      { state := (1 : Fin 2),
        tape := { left := left, head := none, right := [] } } := by
  simp [scanMachine, scanConfig, TM.step, Tape.write, Tape.move]

theorem scan_run_reaches_halt
    (left : List (Option Bool))
    (bits : BitString) :
    scanMachine.halting
      (scanMachine.run (bits.length + 1) (scanConfig left bits)).state = true := by
  induction bits generalizing left with
  | nil =>
      change
        scanMachine.halting
          (scanMachine.run 1 (scanConfig left [])).state = true
      rw [TM.run]
      rw [scanConfig_state]
      rw [scanMachine_not_halted_at_zero]
      rw [scan_step_nil]
      exact scanMachine_halted_at_one
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [scanConfig_state]
      rw [scanMachine_not_halted_at_zero]
      rw [scan_step_cons]
      exact ih (some b :: left)

theorem scan_halts_within_linear
    (bits : BitString) :
    scanMachine.HaltsWithin (bits.length + 1)
      (initialTMConfig scanMachine bits) := by
  have hConfig :
      initialTMConfig scanMachine bits = scanConfig [] bits := by
    cases bits <;> rfl
  rw [hConfig]
  exact scan_run_reaches_halt [] bits

/-- The operational SAT bridge is decomposed into explicit machine-level
    obligations rather than hidden behind one opaque existence field. -/
structure ParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

structure WitnessGuessMachineCertificate where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

structure VerifierMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

/-- Exact remaining composition target: a concrete canonical NTM realization
    of SATBits. No inhabitant is postulated here. -/
def CanonicalSATMachineClosure : Prop :=
  CanonicalSATBoundary.SATInNPGap
    CanonicalCircuitBits.circuitBitEncoding

theorem canonical_sat_machine_closure_gives_bridge
    (h : CanonicalSATMachineClosure) :
    CanonicalSATOperationalGap := by
  exact ⟨{ realization := h }⟩

#print axioms MCore.Real.CanonicalSATNTMAttack.scan_step_cons
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_step_nil
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_run_reaches_halt
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_halts_within_linear
#print axioms MCore.Real.CanonicalSATNTMAttack.canonical_sat_machine_closure_gives_bridge

end CanonicalSATNTMAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATNatParserAttack.lean BLOB 04bd08e97f24e76cab6403b7bc8753c7f751f5d1 -/
import MCore.Real.CanonicalSATParserAttack

namespace MCore
namespace Real
namespace CanonicalSATNatParserAttack

open CanonicalFinalProof
open CanonicalCircuitBits

/-- Three-state unary payload scanner for CanonicalCircuitBits.encodeNat.
    0 scans unary true bits, 1 accepts at the false terminator,
    2 rejects a truncated payload ending at blank. -/
def natScanMachine : TM (Fin 3) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true  => (0, some true, .right)
        | some false => (1, some false, .stay)
        | none       => (2, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 1) || (q == 2) }

@[simp] theorem natScan_not_halted_zero :
    natScanMachine.halting (0 : Fin 3) = false := by
  decide

@[simp] theorem natScan_halted_one :
    natScanMachine.halting (1 : Fin 3) = true := by
  decide

@[simp] theorem natScan_halted_two :
    natScanMachine.halting (2 : Fin 3) = true := by
  decide

def natConfig
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 3) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem natConfig_state
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    (natConfig q left bits).state = q := by
  cases bits <;> rfl

theorem nat_step_true
    (left : List (Option Bool))
    (rest : BitString) :
    natScanMachine.step (natConfig 0 left (true :: rest)) =
      natConfig 0 (some true :: left) rest := by
  cases rest <;>
    simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_step_false
    (left : List (Option Bool))
    (rest : BitString) :
    natScanMachine.step (natConfig 0 left (false :: rest)) =
      natConfig 1 left (false :: rest) := by
  simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_step_blank_rejects
    (left : List (Option Bool)) :
    natScanMachine.step (natConfig 0 left []) =
      natConfig 2 left [] := by
  simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_run_encodeNat_state
    (left : List (Option Bool))
    (n : Nat)
    (tail : BitString) :
    (natScanMachine.run (n + 1)
      (natConfig 0 left (encodeNat n ++ tail))).state = (1 : Fin 3) := by
  induction n generalizing left with
  | zero =>
      simp only [encodeNat, List.cons_append]
      rw [TM.run, natConfig_state, natScan_not_halted_zero]
      rw [nat_step_false]
      simp [TM.run, natConfig]
  | succ n ih =>
      simp only [encodeNat, List.cons_append]
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [TM.run, natConfig_state, natScan_not_halted_zero]
      rw [nat_step_true]
      exact ih (some true :: left)

theorem nat_scan_encodeNat_halts_linear
    (n : Nat)
    (tail : BitString) :
    natScanMachine.HaltsWithin (n + 1)
      (natConfig 0 [] (encodeNat n ++ tail)) := by
  rw [TM.HaltsWithin]
  have hState := nat_run_encodeNat_state [] n tail
  rw [hState]
  exact natScan_halted_one

/-- Truncated unary payload fails immediately once blank is reached. -/
theorem nat_scan_blank_rejects :
    (natScanMachine.run 1 (natConfig 0 [] [])).state = (2 : Fin 3) := by
  rw [TM.run, natConfig_state, natScan_not_halted_zero]
  rw [nat_step_blank_rejects]
  simp [TM.run, natConfig]

/-- After fixed-tag recognition and unary-index scanning, the remaining parser
    frontier is recursive constructor-frame bookkeeping on the canonical tape. -/
structure RecursiveFrameMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def RecursiveFrameOperationalGap : Prop :=
  Nonempty RecursiveFrameMachineCertificate

#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_true
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_false
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_blank_rejects
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_run_encodeNat_state
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_scan_encodeNat_halts_linear
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_scan_blank_rejects

end CanonicalSATNatParserAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATParserAttack.lean BLOB 1b631109f1a2e5f217320fc38dd70cdce6f37c0a -/
import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace CanonicalSATParserAttack

open CanonicalFinalProof

/-- Final states for the six constructor tags in CanonicalCircuitBits.encodeCircuit.
    State 12 is the malformed/truncated-tag sink. -/
def tagMachine : TM (Fin 13) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, symbol, .right)
        | some true  => (2, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 1 then
        match symbol with
        | some false => (3, symbol, .right)
        | some true  => (4, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 2 then
        match symbol with
        | some false => (5, symbol, .right)
        | _          => (12, symbol, .stay)
      else if q = 3 then
        match symbol with
        | some false => (6, symbol, .right)
        | some true  => (7, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 4 then
        match symbol with
        | some false => (8, symbol, .right)
        | some true  => (9, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 5 then
        match symbol with
        | some false => (10, symbol, .right)
        | some true  => (11, symbol, .right)
        | none       => (12, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => decide (6 ≤ q.val) }

@[simp] theorem tagMachine_initial_not_halted :
    tagMachine.halting (0 : Fin 13) = false := by
  decide

def tagInput (bitsPrefix : List Bool) (tail : BitString) : BitString :=
  bitsPrefix ++ tail

def tagConfig
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 13) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem tagConfig_state
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    (tagConfig q left bits).state = q := by
  cases bits <;> rfl

theorem initial_tagConfig
    (bits : BitString) :
    initialTMConfig tagMachine bits = tagConfig 0 [] bits := by
  cases bits <;> rfl

@[simp] theorem tagMachine_not_halted_at_one :
    tagMachine.halting (1 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_two :
    tagMachine.halting (2 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_three :
    tagMachine.halting (3 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_four :
    tagMachine.halting (4 : Fin 13) = false := by decide
@[simp] theorem tagMachine_not_halted_at_five :
    tagMachine.halting (5 : Fin 13) = false := by decide
@[simp] theorem tagMachine_halted_at_twelve :
    tagMachine.halting (12 : Fin 13) = true := by decide

theorem tag_step_0_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 0 left (false :: rest)) =
      tagConfig 1 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_0_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 0 left (true :: rest)) =
      tagConfig 2 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_1_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 1 left (false :: rest)) =
      tagConfig 3 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_1_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 1 left (true :: rest)) =
      tagConfig 4 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_2_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 2 left (false :: rest)) =
      tagConfig 5 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_2_true_sink
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 2 left (true :: rest)) =
      tagConfig 12 left (true :: rest) := by
  simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_3_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 3 left (false :: rest)) =
      tagConfig 6 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_3_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 3 left (true :: rest)) =
      tagConfig 7 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_4_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 4 left (false :: rest)) =
      tagConfig 8 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_4_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 4 left (true :: rest)) =
      tagConfig 9 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_5_false
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 5 left (false :: rest)) =
      tagConfig 10 (some false :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_step_5_true
    (left : List (Option Bool)) (rest : BitString) :
    tagMachine.step (tagConfig 5 left (true :: rest)) =
      tagConfig 11 (some true :: left) rest := by
  cases rest <;>
    simp [tagMachine, tagConfig, TM.step, Tape.write, Tape.move]

theorem tag_input_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, false] tail))).state = (6 : Fin 13) := by
  rw [show tagInput [false, false, false] tail = false :: false :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_three, tag_step_3_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_false_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, true] tail))).state = (7 : Fin 13) := by
  rw [show tagInput [false, false, true] tail = false :: false :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_three, tag_step_3_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_true_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, false] tail))).state = (8 : Fin 13) := by
  rw [show tagInput [false, true, false] tail = false :: true :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_four, tag_step_4_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_not_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, true] tail))).state = (9 : Fin 13) := by
  rw [show tagInput [false, true, true] tail = false :: true :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_one, tag_step_1_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_four, tag_step_4_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_and_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, false] tail))).state = (10 : Fin 13) := by
  rw [show tagInput [true, false, false] tail = true :: false :: false :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_five, tag_step_5_false]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_or_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, true] tail))).state = (11 : Fin 13) := by
  rw [show tagInput [true, false, true] tail = true :: false :: true :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_false]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_five, tag_step_5_true]
  simp [TM.run, tagConfig]
  cases tail <;> rfl

theorem tag_invalid_11_rejects
    (third : Bool)
    (tail : BitString) :
    (tagMachine.run 2
      (initialTMConfig tagMachine
        (tagInput [true, true, third] tail))).state = (12 : Fin 13) := by
  rw [show tagInput [true, true, third] tail = true :: true :: third :: tail by
    simp [tagInput]]
  rw [initial_tagConfig]
  rw [TM.run, tagConfig_state, tagMachine_initial_not_halted, tag_step_0_true]
  rw [TM.run, tagConfig_state, tagMachine_not_halted_at_two, tag_step_2_true_sink]
  simp [TM.run, tagConfig]

/-- The finite tag decoder is now concrete. The remaining parser obligation is
    unbounded recursive syntax bookkeeping on the same single tape. -/
structure RecursiveParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def RecursiveParserOperationalGap : Prop :=
  Nonempty RecursiveParserMachineCertificate

/-- Fail-proof: the legacy recursive-parser gate is under-specified.  A halted
    one-state machine inhabits it without recognizing a single constructor. -/
theorem legacy_recursive_parser_gate_is_trivially_inhabited :
    RecursiveParserOperationalGap := by
  let trivialMachine : TM (Fin 1) (Option Bool) :=
    { initial := 0
      blank := none
      transition := fun q symbol => (q, symbol, .stay)
      halting := fun _ => true }
  have hpoly : PolynomialTimeBound (fun _ => 0) := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp
  exact ⟨
    { stateCount := 0
      machine := trivialMachine
      timeBound := fun _ => 0
      time_poly := hpoly }⟩

/-- Hardened recursive parser boundary.  A witness must halt in polynomial
    time on every canonical bit tape and its accepting state must agree exactly
    with the total functional decoder.  This is the operational content that
    the legacy existence-only structure did not express. -/
structure CanonicalRecursiveParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ bits : BitString,
      machine.HaltsWithin
        (timeBound bits.length)
        (initialTMConfig machine bits)

  correct :
    ∀ bits : BitString,
      accepting
          (machine.run
            (timeBound bits.length)
            (initialTMConfig machine bits)).state = true
        ↔
      ∃ φ : CircuitK1.Circuit,
        CanonicalCircuitBits.decodeCircuit bits = some φ

def CanonicalRecursiveParserOperationalGap : Prop :=
  Nonempty CanonicalRecursiveParserMachineCertificate

/-- A genuine hardened parser also supplies the old existence-only payload.
    The converse is intentionally unavailable. -/
def CanonicalRecursiveParserMachineCertificate.toLegacy
    (C : CanonicalRecursiveParserMachineCertificate) :
    RecursiveParserMachineCertificate :=
  { stateCount := C.stateCount
    machine := C.machine
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem canonical_recursive_parser_closes_legacy_gap
    (h : CanonicalRecursiveParserOperationalGap) :
    RecursiveParserOperationalGap := by
  rcases h with ⟨C⟩
  exact ⟨C.toLegacy⟩

#print axioms MCore.Real.CanonicalSATParserAttack.legacy_recursive_parser_gate_is_trivially_inhabited
#print axioms MCore.Real.CanonicalSATParserAttack.canonical_recursive_parser_closes_legacy_gap

#print axioms MCore.Real.CanonicalSATParserAttack.tag_input_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_false_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_true_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_not_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_and_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_or_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_invalid_11_rejects

end CanonicalSATParserAttack
end Real
end MCore


/- SOURCE lean/MCore/Real/CanonicalSATVerifier.lean BLOB 286211091577d66ca401c618fcac6ee91c02f9d0 -/
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace CanonicalSATVerifier

open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness

def verifyWitness
    (φ : Circuit)
    (w : SATWitness φ) : Bool :=
  Bool.and
    (isCNFBool φ)
    (evalCircuit (assignmentOfWitness φ w) φ)

theorem verifyWitness_correct
    (φ : Circuit)
    (w : SATWitness φ) :
    verifyWitness φ w = true ↔ SATWitnessAccepts φ w := by
  unfold verifyWitness SATWitnessAccepts
  rw [bool_and_eq_true_iff]
  rw [isCNFBool_eq_true_iff]

/-- Structural work budget for the high-level verifier. This is NOT yet a
    theorem about canonical Turing-machine steps. -/
def verificationCost (φ : Circuit) : Nat :=
  CircuitK1.size φ + varBound φ

theorem verificationCost_linear_encoding_bound
    (φ : Circuit) :
    verificationCost φ ≤ 2 * (encodeCircuit φ).length := by
  unfold verificationCost
  have hs := size_le_encodeCircuit_length φ
  have hv := varBound_le_encoded_length φ
  omega

theorem sat_has_short_verified_witness
    (φ : Circuit) :
    SATLanguage φ ↔
      ∃ w : SATWitness φ,
        verifyWitness φ w = true ∧
        (witnessBits w).length ≤ (encodeCircuit φ).length := by
  constructor
  · intro hSAT
    rcases (satLanguage_iff_exists_finite_witness φ).mp hSAT with ⟨w, hw⟩
    refine ⟨w, (verifyWitness_correct φ w).mpr hw, witness_bits_linear_bound w⟩
  · rintro ⟨w, hVerify, _⟩
    exact (satLanguage_iff_exists_finite_witness φ).mpr
      ⟨w, (verifyWitness_correct φ w).mp hVerify⟩

/-- Exact remaining G1 operational bridge after encoding+witness+verifier. -/
structure VerifierToCanonicalNTMBridge where
  realization :
    CanonicalSATBoundary.SATInNPGap
      CanonicalCircuitBits.circuitBitEncoding

def CanonicalSATOperationalGap : Prop :=
  Nonempty VerifierToCanonicalNTMBridge

theorem operational_bridge_closes_sat_in_np
    (B : VerifierToCanonicalNTMBridge) :
    CanonicalSATBoundary.SATInNPGap
      CanonicalCircuitBits.circuitBitEncoding :=
  B.realization

#print axioms MCore.Real.CanonicalSATVerifier.verifyWitness_correct
#print axioms MCore.Real.CanonicalSATVerifier.verificationCost_linear_encoding_bound
#print axioms MCore.Real.CanonicalSATVerifier.sat_has_short_verified_witness
#print axioms MCore.Real.CanonicalSATVerifier.operational_bridge_closes_sat_in_np

end CanonicalSATVerifier
end Real
end MCore

