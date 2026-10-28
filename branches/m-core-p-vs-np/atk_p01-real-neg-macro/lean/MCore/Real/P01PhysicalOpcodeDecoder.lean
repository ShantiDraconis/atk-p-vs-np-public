import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01PhysicalOpcodeDecoder

open CanonicalFinalProof

/--
Fixed three-bit canonical opcode decoder.
States:
0 start
1 saw 0
2 saw 1
3 saw 00
4 saw 01
5 saw 10
6 input
7 constFalse
8 constTrue
9 neg
10 and
11 or
12 reject
-/
abbrev OpcodeState := Fin 13

def start : OpcodeState := 0
def saw0 : OpcodeState := 1
def saw1 : OpcodeState := 2
def saw00 : OpcodeState := 3
def saw01 : OpcodeState := 4
def saw10 : OpcodeState := 5
def inputHalt : OpcodeState := 6
def constFalseHalt : OpcodeState := 7
def constTrueHalt : OpcodeState := 8
def negHalt : OpcodeState := 9
def andHalt : OpcodeState := 10
def orHalt : OpcodeState := 11
def rejectHalt : OpcodeState := 12

def opcodeDecoderMachine : TM OpcodeState (Option Bool) :=
  { initial := start
    blank := none
    transition := fun q symbol =>
      if q = start then
        match symbol with
        | some false => (saw0, some false, .right)
        | some true  => (saw1, some true, .right)
        | none       => (rejectHalt, none, .stay)
      else if q = saw0 then
        match symbol with
        | some false => (saw00, some false, .right)
        | some true  => (saw01, some true, .right)
        | none       => (rejectHalt, none, .stay)
      else if q = saw1 then
        match symbol with
        | some false => (saw10, some false, .right)
        | _          => (rejectHalt, symbol, .stay)
      else if q = saw00 then
        match symbol with
        | some false => (inputHalt, some false, .right)
        | some true  => (constFalseHalt, some true, .right)
        | none       => (rejectHalt, none, .stay)
      else if q = saw01 then
        match symbol with
        | some false => (constTrueHalt, some false, .right)
        | some true  => (negHalt, some true, .right)
        | none       => (rejectHalt, none, .stay)
      else if q = saw10 then
        match symbol with
        | some false => (andHalt, some false, .right)
        | some true  => (orHalt, some true, .right)
        | none       => (rejectHalt, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q =>
      (q == inputHalt) || (q == constFalseHalt) ||
      (q == constTrueHalt) || (q == negHalt) ||
      (q == andHalt) || (q == orHalt) || (q == rejectHalt) }

@[simp] theorem opcodeDecoderMachine_blank :
    opcodeDecoderMachine.blank = none := rfl

def tagTape (a b c : Bool) : Tape (Option Bool) :=
  { left := [], head := some a, right := [some b, some c] }

def opcodeConfig (a b c : Bool) : Configuration OpcodeState (Option Bool) :=
  { state := opcodeDecoderMachine.initial, tape := tagTape a b c }

theorem decode_input_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig false false false)).state =
      inputHalt := by
  decide

theorem decode_const_false_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig false false true)).state =
      constFalseHalt := by
  decide

theorem decode_const_true_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig false true false)).state =
      constTrueHalt := by
  decide

theorem decode_neg_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig false true true)).state =
      negHalt := by
  decide

theorem decode_and_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig true false false)).state =
      andHalt := by
  decide

theorem decode_or_tag :
    (opcodeDecoderMachine.run 3 (opcodeConfig true false true)).state =
      orHalt := by
  decide

theorem decode_invalid_110 :
    (opcodeDecoderMachine.run 2 (opcodeConfig true true false)).state =
      rejectHalt := by
  decide

theorem decode_invalid_111 :
    (opcodeDecoderMachine.run 2 (opcodeConfig true true true)).state =
      rejectHalt := by
  decide

#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_input_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_const_false_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_const_true_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_neg_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_and_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_or_tag
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_invalid_110
#print axioms MCore.Real.P01PhysicalOpcodeDecoder.decode_invalid_111

end P01PhysicalOpcodeDecoder
end Real
end MCore
