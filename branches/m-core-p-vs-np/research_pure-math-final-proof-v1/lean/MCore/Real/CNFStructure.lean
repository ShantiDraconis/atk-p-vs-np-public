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

/-- Base-level probe for the decimal representation API actually shipped in Lean 4.19. -/
theorem toDigits_unfold (n : Nat) :
    Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] := rfl

/-- The local decoder agrees with the ten canonical decimal digit characters.
    Written without optional tactics or post-4.19 ToString lemmas. -/
theorem charToDigit_digitChar_decimal :
    (∀ d : Nat, d < 10 → charToDigit? (Nat.digitChar d) = some d) := by
  intro d hd
  rcases Nat.lt_or_ge d 1 with h0 | h0
  · have : d = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h0)
    subst d; rfl
  rcases Nat.lt_or_ge d 2 with h1 | h1
  · have : d = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1) h0
    subst d; rfl
  rcases Nat.lt_or_ge d 3 with h2 | h2
  · have : d = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h2) h1
    subst d; rfl
  rcases Nat.lt_or_ge d 4 with h3 | h3
  · have : d = 3 := Nat.le_antisymm (Nat.le_of_lt_succ h3) h2
    subst d; rfl
  rcases Nat.lt_or_ge d 5 with h4 | h4
  · have : d = 4 := Nat.le_antisymm (Nat.le_of_lt_succ h4) h3
    subst d; rfl
  rcases Nat.lt_or_ge d 6 with h5 | h5
  · have : d = 5 := Nat.le_antisymm (Nat.le_of_lt_succ h5) h4
    subst d; rfl
  rcases Nat.lt_or_ge d 7 with h6 | h6
  · have : d = 6 := Nat.le_antisymm (Nat.le_of_lt_succ h6) h5
    subst d; rfl
  rcases Nat.lt_or_ge d 8 with h7 | h7
  · have : d = 7 := Nat.le_antisymm (Nat.le_of_lt_succ h7) h6
    subst d; rfl
  rcases Nat.lt_or_ge d 9 with h8 | h8
  · have : d = 8 := Nat.le_antisymm (Nat.le_of_lt_succ h8) h7
    subst d; rfl
  · have : d = 9 := Nat.le_antisymm (Nat.le_of_lt_succ hd) h8
    subst d; rfl

/-- A one-digit decimal numeral is decoded exactly. -/
theorem parseNatChars_single_digit {d : Nat} (hd : d < 10) :
    parseNatChars [Nat.digitChar d] 0 false = some (d, []) := by
  simp [parseNatChars, charToDigit_digitChar_decimal d hd]

/-- A canonical decimal digit can be consumed from an arbitrary accumulator and tail. -/
theorem parseNatChars_cons_digit {d acc : Nat} {tail : List Char} (hd : d < 10) :
    parseNatChars (Nat.digitChar d :: tail) acc false =
      parseNatChars tail (10 * acc + d) true := by
  simp [parseNatChars, charToDigit_digitChar_decimal d hd]

/-- Consuming a canonical decimal digit is independent of the incoming seen flag. -/
theorem parseNatChars_cons_digit_seen {d acc : Nat} {tail : List Char} {seen : Bool}
    (hd : d < 10) :
    parseNatChars (Nat.digitChar d :: tail) acc seen =
      parseNatChars tail (10 * acc + d) true := by
  simp [parseNatChars, charToDigit_digitChar_decimal d hd]

/-- First recursive probe against the representation primitive shipped by Lean 4.19:
    when the quotient is zero, toDigitsCore emits exactly the final digit. -/
theorem parseNatChars_toDigitsCore_terminal {n fuel acc : Nat}
    (hn : n < 10) (hf : fuel > 0) :
    parseNatChars (Nat.toDigitsCore 10 fuel n []) acc false =
      some (10 * acc + n, []) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      have hmod : n % 10 = n := Nat.mod_eq_of_lt hn
      simp [Nat.toDigitsCore, Nat.div_eq_of_lt hn, hmod,
        charToDigit_digitChar_decimal n hn, parseNatChars]

/-- Recursive representation probe: for a nonterminal decimal numeral, expose the
    quotient/remainder step used by Lean 4.19 toDigitsCore. -/
theorem toDigitsCore_decimal_step {n fuel : Nat}
    (hf : fuel > 0) (hn : 10 ≤ n) :
    Nat.toDigitsCore 10 fuel n [] =
      Nat.toDigitsCore 10 (fuel - 1) (n / 10) [Nat.digitChar (n % 10)] := by
  cases fuel with
  | zero => omega
  | succ k =>
      simp [Nat.toDigitsCore, Nat.ne_of_gt (Nat.div_pos hn (by decide))]

/-- The representation recursion strictly decreases its numeric argument once the
    numeral has at least two decimal digits.  This is the induction measure
    needed by the full decimal parser invariant. -/
theorem toDigitsCore_decimal_decreases {n : Nat} (hn : 10 ≤ n) :
    n / 10 < n := by
  exact Nat.div_lt_self (by omega) (by decide)

/-- One recursive decimal representation step exposes the strictly smaller quotient.
    This packages the representation equation and its induction measure for the
    forthcoming parser invariant. -/
theorem toDigitsCore_decimal_step_decreases {n fuel : Nat}
    (hf : fuel > 0) (hn : 10 ≤ n) :
    Nat.toDigitsCore 10 fuel n [] =
        Nat.toDigitsCore 10 (fuel - 1) (n / 10) [Nat.digitChar (n % 10)] ∧
      n / 10 < n := by
  exact ⟨toDigitsCore_decimal_step hf hn, toDigitsCore_decimal_decreases hn⟩

/-- Every nonterminal decimal recursion step keeps the emitted digit in base 10.
    This is the digit-side invariant needed when the parser consumes the
    recursive representation. -/
theorem toDigitsCore_decimal_mod_lt {n : Nat} :
    n % 10 < 10 := by
  exact Nat.mod_lt n (by decide)

/-- Parser-side invariant for appending one canonical decimal digit after a
    successfully accumulated prefix.  This is the algebraic step used by the
    general representation/parser induction. -/
theorem parseNatChars_append_digit {d acc : Nat} (hd : d < 10) :
    parseNatChars [Nat.digitChar d] acc true =
      some (10 * acc + d, []) := by
  simp [parseNatChars, charToDigit_digitChar_decimal d hd]

/-- Parsing a canonical decimal digit in front of a tail is exactly the
    accumulator update, independently of the incoming seen flag.  This is the
    parser-side compositional invariant used by the full toDigitsCore induction. -/
theorem parseNatChars_digit_tail {d acc : Nat} {tail : List Char} {seen : Bool}
    (hd : d < 10) :
    parseNatChars (Nat.digitChar d :: tail) acc seen =
      parseNatChars tail (10 * acc + d) true := by
  exact parseNatChars_cons_digit_seen hd

/-- Exact parser invariant for any list of canonical decimal digits:
    parsing from an accumulator is equivalent to folding the base-10 update
    across the digit values.  This is independent of Nat.toDigitsCore and is
    the compositional parser half of the representation roundtrip. -/
theorem parseNatChars_digit_list
    (ds : List Nat) (acc : Nat) (seen : Bool)
    (hds : ∀ d ∈ ds, d < 10) :
    parseNatChars (ds.map Nat.digitChar) acc seen =
      if ds = [] then
        (if seen then some (acc, []) else none)
      else
        some (ds.foldl (fun a d => 10 * a + d) acc, []) := by
  induction ds generalizing acc seen with
  | nil =>
      simp [parseNatChars]
  | cons d ds ih =>
      have hd : d < 10 := hds d (by simp)
      have htail : ∀ e ∈ ds, e < 10 := by
        intro e he
        exact hds e (by simp [he])
      rw [List.map_cons, parseNatChars_digit_tail hd]
      cases ds with
      | nil =>
          simp [parseNatChars]
      | cons e es =>
          simp only [List.foldl_cons]
          have hi := ih (acc := 10 * acc + d) (seen := true) htail
          simpa using hi

/-- Concrete bridge target from Lean's decimal representation primitive to
    the parser: the canonical base-10 digit list must fold back to the original
    natural number.  Kept explicit so the next proof attempt tests the real
    representation boundary rather than another parser-only lemma. -/
def ToDigitsFoldRoundtrip : Prop :=
  ∀ n : Nat,
    (Nat.toDigits 10 n).foldl
      (fun acc ch =>
        match charToDigit? ch with
        | some d => 10 * acc + d
        | none => acc) 0 = n

/-- The exact theorem target at the representation boundary.  Unlike the
    proposition-valued frontier marker, this declaration must construct the
    roundtrip proof from Lean's actual Nat.toDigits implementation. -/
theorem toDigitsFoldRoundtrip_target :
    ToDigitsFoldRoundtrip := by
  intro n
  unfold Nat.toDigits
  have hdigits :
      ∀ fuel n acc,
        fuel > n →
        (Nat.toDigitsCore 10 fuel n []).foldl
          (fun a ch =>
            match charToDigit? ch with
            | some d => 10 * a + d
            | none => a) acc =
          acc * 10 ^ (Nat.toDigitsCore 10 fuel n []).length + n := by
    intro fuel
    induction fuel with
    | zero =>
        intro n acc hf
        omega
    | succ fuel ih =>
        intro n acc hf
        rw [Nat.toDigitsCore]
        by_cases hq : n / 10 = 0
        · simp [hq, charToDigit_digitChar_decimal, Nat.mod_lt n (by decide)]
          omega
        · simp [hq]
          omega
  simpa using hdigits (n + 1) n 0 (by omega)

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
