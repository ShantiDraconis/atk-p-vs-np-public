import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore
namespace Real
namespace CanonicalSATSlotParserSpec

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse

/-- One constructor token with exactly the finite information carried by its
tag/payload. Child circuits are never stored in the token. -/
inductive Head where
  | input : Nat → Head
  | const : Bool → Head
  | not : Head
  | and : Head
  | or : Head
  deriving DecidableEq, Repr

namespace Head

def arity : Head → Nat
  | .input _ => 0
  | .const _ => 0
  | .not => 1
  | .and => 2
  | .or => 2

def encode : Head → BitString
  | .input i => [false, false, false] ++ encodeNat i
  | .const false => [false, false, true]
  | .const true => [false, true, false]
  | .not => [false, true, true]
  | .and => [true, false, false]
  | .or => [true, false, true]

end Head

/-- Parse one constructor head. INPUT consumes its unary index payload; the
remaining recursive children stay on the bitstring. -/
def parseHead : BitString → Option (Head × BitString)
  | false :: false :: false :: rest =>
      match decodeNat rest with
      | some (i, tail) => some (.input i, tail)
      | none => none
  | false :: false :: true :: rest => some (.const false, rest)
  | false :: true :: false :: rest => some (.const true, rest)
  | false :: true :: true :: rest => some (.not, rest)
  | true :: false :: false :: rest => some (.and, rest)
  | true :: false :: true :: rest => some (.or, rest)
  | _ => none

/-- Compatibility view used by the operational design: only the arity is
needed to update the outstanding-slot counter. -/
def tokenArity (bits : BitString) : Option (Nat × BitString) :=
  match parseHead bits with
  | none => none
  | some (h, tail) => some (h.arity, tail)

/-- Successful token parsing determines the exact consumed canonical head. -/
theorem parseHead_inverse
    (bits : BitString)
    (h : Head)
    (tail : BitString)
    (hp : parseHead bits = some (h, tail)) :
    bits = h.encode ++ tail := by
  cases bits with
  | nil =>
      simp [parseHead] at hp
  | cons b1 r1 =>
      cases r1 with
      | nil =>
          simp [parseHead] at hp
      | cons b2 r2 =>
          cases r2 with
          | nil =>
              simp [parseHead] at hp
          | cons b3 rest =>
              cases b1 <;> cases b2 <;> cases b3
              · cases hn : decodeNat rest with
                | none =>
                    simp [parseHead, hn] at hp
                | some p =>
                    rcases p with ⟨i, t⟩
                    simp [parseHead, hn] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    have hNat := decodeNat_inverse rest i t hn
                    simp [Head.encode, hNat, List.append_assoc]
              · simp [parseHead] at hp
                rcases hp with ⟨rfl, rfl⟩
                rfl
              · simp [parseHead] at hp
                rcases hp with ⟨rfl, rfl⟩
                rfl
              · simp [parseHead] at hp
                rcases hp with ⟨rfl, rfl⟩
                rfl
              · simp [parseHead] at hp
                rcases hp with ⟨rfl, rfl⟩
                rfl
              · simp [parseHead] at hp
                rcases hp with ⟨rfl, rfl⟩
                rfl
              · simp [parseHead] at hp
              · simp [parseHead] at hp

/-- Prefix-tree slot recognizer. The slot count is the number of subtrees still
required. A token consumes one slot and opens h.arity new slots. -/
def slotParseCore : Nat → Nat → BitString → Bool
  | 0, _, _ => false
  | _ + 1, 0, bits => bits.isEmpty
  | fuel + 1, slots + 1, bits =>
      match parseHead bits with
      | none => false
      | some (h, rest) =>
          slotParseCore fuel (slots + h.arity) rest

def slotAccept (bits : BitString) : Bool :=
  slotParseCore (bits.length + 1) 1 bits

@[simp] theorem parseHead_input
    (i : Nat) (tail : BitString) :
    parseHead (encodeCircuit (.input i) ++ tail) = some (.input i, tail) := by
  simp [parseHead, encodeCircuit, decodeNat_encodeNat_append, List.append_assoc]

@[simp] theorem parseHead_const
    (b : Bool) (tail : BitString) :
    parseHead (encodeCircuit (.const b) ++ tail) = some (.const b, tail) := by
  cases b <;> simp [parseHead, encodeCircuit]

@[simp] theorem parseHead_not
    (c : Circuit) (tail : BitString) :
    parseHead (encodeCircuit (.not c) ++ tail) =
      some (.not, encodeCircuit c ++ tail) := by
  simp [parseHead, encodeCircuit, List.append_assoc]

@[simp] theorem parseHead_and
    (a b : Circuit) (tail : BitString) :
    parseHead (encodeCircuit (.and a b) ++ tail) =
      some (.and, encodeCircuit a ++ encodeCircuit b ++ tail) := by
  simp [parseHead, encodeCircuit, List.append_assoc]

@[simp] theorem parseHead_or
    (a b : Circuit) (tail : BitString) :
    parseHead (encodeCircuit (.or a b) ++ tail) =
      some (.or, encodeCircuit a ++ encodeCircuit b ++ tail) := by
  simp [parseHead, encodeCircuit, List.append_assoc]

/-- Parsing one canonical circuit consumes exactly size c macro steps and one
outstanding slot, independently of the surrounding forest. -/
theorem slotParseCore_encode_append
    (c : Circuit)
    (tail : BitString)
    (slots fuel : Nat) :
    slotParseCore (CircuitK1.size c + fuel) (slots + 1)
        (encodeCircuit c ++ tail) =
      slotParseCore fuel slots tail := by
  induction c generalizing tail slots fuel with
  | input i =>
      have hFuel : CircuitK1.size (.input i) + fuel = fuel + 1 := by
        simp [CircuitK1.size, Nat.add_comm]
      rw [hFuel]
      simp [slotParseCore, parseHead_input, Head.arity]
  | const b =>
      have hFuel : CircuitK1.size (.const b) + fuel = fuel + 1 := by
        simp [CircuitK1.size, Nat.add_comm]
      rw [hFuel]
      cases b <;> simp [slotParseCore, parseHead_const, Head.arity]
  | not c ih =>
      have hFuel :
          CircuitK1.size (.not c) + fuel =
            (CircuitK1.size c + fuel) + 1 := by
        simp [CircuitK1.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [hFuel]
      simp only [slotParseCore]
      rw [parseHead_not]
      simp only [Head.arity]
      exact ih tail slots fuel
  | and a b iha ihb =>
      have hFuel :
          CircuitK1.size (.and a b) + fuel =
            (CircuitK1.size a + (CircuitK1.size b + fuel)) + 1 := by
        simp [CircuitK1.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [hFuel]
      simp only [slotParseCore]
      rw [parseHead_and]
      simp only [Head.arity]
      have ha :=
        iha (encodeCircuit b ++ tail) (slots + 1)
          (CircuitK1.size b + fuel)
      have hb := ihb tail slots fuel
      rw [show slots + 2 = (slots + 1) + 1 by simp [Nat.add_assoc]]
      rw [show
          encodeCircuit a ++ encodeCircuit b ++ tail =
            encodeCircuit a ++ (encodeCircuit b ++ tail) by
          simp [List.append_assoc]]
      rw [ha]
      exact hb
  | or a b iha ihb =>
      have hFuel :
          CircuitK1.size (.or a b) + fuel =
            (CircuitK1.size a + (CircuitK1.size b + fuel)) + 1 := by
        simp [CircuitK1.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [hFuel]
      simp only [slotParseCore]
      rw [parseHead_or]
      simp only [Head.arity]
      have ha :=
        iha (encodeCircuit b ++ tail) (slots + 1)
          (CircuitK1.size b + fuel)
      have hb := ihb tail slots fuel
      rw [show slots + 2 = (slots + 1) + 1 by simp [Nat.add_assoc]]
      rw [show
          encodeCircuit a ++ encodeCircuit b ++ tail =
            encodeCircuit a ++ (encodeCircuit b ++ tail) by
          simp [List.append_assoc]]
      rw [ha]
      exact hb

theorem slotAccept_encodeCircuit
    (c : Circuit) :
    slotAccept (encodeCircuit c) = true := by
  have hSize :
      CircuitK1.size c ≤ (encodeCircuit c).length :=
    size_le_encodeCircuit_length c
  let extra := (encodeCircuit c).length - CircuitK1.size c
  have hDecomp :
      CircuitK1.size c + extra = (encodeCircuit c).length := by
    exact Nat.add_sub_of_le hSize
  have hEq :
      (encodeCircuit c).length + 1 =
        CircuitK1.size c + (extra + 1) := by
    calc
      (encodeCircuit c).length + 1 =
          (CircuitK1.size c + extra) + 1 := by rw [hDecomp]
      _ = CircuitK1.size c + (extra + 1) := by
          simp [Nat.add_assoc]
  unfold slotAccept
  rw [hEq]
  have hParse :=
    slotParseCore_encode_append c [] 0 (extra + 1)
  simpa [slotParseCore] using hParse

def encodeForest : List Circuit → BitString
  | [] => []
  | c :: cs => encodeCircuit c ++ encodeForest cs

def ForestEncoded (slots : Nat) (bits : BitString) : Prop :=
  ∃ cs : List Circuit, cs.length = slots ∧ bits = encodeForest cs

/-- Soundness of the slot discipline: successful parsing with k slots means
the entire bitstring is exactly a forest of k canonical circuits. -/
theorem slotParseCore_sound
    (fuel slots : Nat)
    (bits : BitString)
    (h : slotParseCore fuel slots bits = true) :
    ForestEncoded slots bits := by
  induction fuel generalizing slots bits with
  | zero =>
      simp [slotParseCore] at h
  | succ fuel ih =>
      cases slots with
      | zero =>
          cases bits with
          | nil =>
              exact ⟨[], rfl, rfl⟩
          | cons b bs =>
              simp [slotParseCore] at h
      | succ slots =>
          cases hp : parseHead bits with
          | none =>
              simp [slotParseCore, hp] at h
          | some p =>
              rcases p with ⟨head, restBits⟩
              have hrec :
                  slotParseCore fuel (slots + head.arity) restBits = true := by
                simpa [slotParseCore, hp] using h
              rcases ih (slots + head.arity) restBits hrec with
                ⟨cs, hlen, henc⟩
              have hbits : bits = head.encode ++ restBits :=
                parseHead_inverse bits head restBits hp
              cases head with
              | input i =>
                  have hlen' : cs.length = slots := by
                    simpa [Head.arity] using hlen
                  refine ⟨.input i :: cs, ?_, ?_⟩
                  · simp [hlen']
                  · rw [hbits, henc]
                    simp [Head.encode, encodeForest, encodeCircuit, List.append_assoc]
              | const b =>
                  have hlen' : cs.length = slots := by
                    simpa [Head.arity] using hlen
                  refine ⟨.const b :: cs, ?_, ?_⟩
                  · simp [hlen']
                  · rw [hbits, henc]
                    cases b <;>
                      simp [Head.encode, encodeForest, encodeCircuit, List.append_assoc]
              | not =>
                  have hlen' : cs.length = slots + 1 := by
                    simpa [Head.arity] using hlen
                  cases cs with
                  | nil =>
                      simp at hlen'
                  | cons child rest =>
                      have hrest : rest.length = slots := by
                        simp at hlen'
                        omega
                      refine ⟨.not child :: rest, ?_, ?_⟩
                      · simp [hrest]
                      · rw [hbits, henc]
                        simp [Head.encode, encodeForest, encodeCircuit, List.append_assoc]
              | and =>
                  have hlen' : cs.length = slots + 2 := by
                    simpa [Head.arity] using hlen
                  cases cs with
                  | nil =>
                      simp at hlen'
                  | cons a rest1 =>
                      cases rest1 with
                      | nil =>
                          simp at hlen'
                      | cons b rest =>
                          have hrest : rest.length = slots := by
                            simp at hlen'
                            omega
                          refine ⟨.and a b :: rest, ?_, ?_⟩
                          · simp [hrest]
                          · rw [hbits, henc]
                            simp [Head.encode, encodeForest, encodeCircuit, List.append_assoc]
              | or =>
                  have hlen' : cs.length = slots + 2 := by
                    simpa [Head.arity] using hlen
                  cases cs with
                  | nil =>
                      simp at hlen'
                  | cons a rest1 =>
                      cases rest1 with
                      | nil =>
                          simp at hlen'
                      | cons b rest =>
                          have hrest : rest.length = slots := by
                            simp at hlen'
                            omega
                          refine ⟨.or a b :: rest, ?_, ?_⟩
                          · simp [hrest]
                          · rw [hbits, henc]
                            simp [Head.encode, encodeForest, encodeCircuit, List.append_assoc]

/-- Initial one-slot acceptance is exactly membership in the range of the
canonical Circuit encoding. -/
theorem slotAccept_iff_exists_exact_encoding
    (bits : BitString) :
    slotAccept bits = true ↔ ∃ c : Circuit, bits = encodeCircuit c := by
  constructor
  · intro h
    rcases slotParseCore_sound (bits.length + 1) 1 bits h with
      ⟨cs, hlen, henc⟩
    cases cs with
    | nil =>
        simp at hlen
    | cons c rest =>
        cases rest with
        | nil =>
            exact ⟨c, by simpa [encodeForest] using henc⟩
        | cons d ds =>
            simp at hlen
  · rintro ⟨c, rfl⟩
    exact slotAccept_encodeCircuit c

/-- Exact semantic target for the operational TM: slot acceptance agrees with
the repository's total decoder, including rejection of residual garbage. -/
theorem slotAccept_iff_decodeCircuit
    (bits : BitString) :
    slotAccept bits = true ↔
      ∃ c : Circuit, decodeCircuit bits = some c := by
  exact
    (slotAccept_iff_exists_exact_encoding bits).trans
      (exists_decodeCircuit_iff_exists_exact_encoding bits).symm

theorem slotParse_invalid_11
    (fuel slots : Nat)
    (third : Bool)
    (tail : BitString) :
    slotParseCore (fuel + 1) (slots + 1)
      (true :: true :: third :: tail) = false := by
  simp [slotParseCore, parseHead]

theorem slotParse_truncated_tag
    (fuel slots : Nat)
    (b1 b2 : Bool) :
    slotParseCore (fuel + 1) (slots + 1) [b1, b2] = false := by
  cases b1 <;> cases b2 <;> simp [slotParseCore, parseHead]

theorem decodeNat_replicate_true_none
    (ones : Nat) :
    decodeNat (List.replicate ones true) = none := by
  induction ones with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate_succ, decodeNat, ih]

theorem tokenArity_truncated_input
    (ones : Nat) :
    tokenArity
      ([false, false, false] ++ List.replicate ones true) = none := by
  simp [tokenArity, parseHead, decodeNat_replicate_true_none]

#print axioms MCore.Real.CanonicalSATSlotParserSpec.parseHead_inverse
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParseCore_encode_append
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotAccept_encodeCircuit
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParseCore_sound
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotAccept_iff_exists_exact_encoding
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotAccept_iff_decodeCircuit
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParse_invalid_11

end CanonicalSATSlotParserSpec
end Real
end MCore
