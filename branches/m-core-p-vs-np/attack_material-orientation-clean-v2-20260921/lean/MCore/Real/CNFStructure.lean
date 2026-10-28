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
