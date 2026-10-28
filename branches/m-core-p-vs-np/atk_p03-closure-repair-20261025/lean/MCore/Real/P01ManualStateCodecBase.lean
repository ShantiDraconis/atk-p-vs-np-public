import MCore.Real.P01VerifierStateCode
import MCore.Real.P01CheckedVerifierCompositeNTM

namespace MCore
namespace Real
namespace P01ManualStateCodecBase

open P01VerifierStateCode

/-! Explicit codecs for the finite input/read control.
These are executable left inverses and use no Fintype enumeration. -/

def lookaheadCode : P01InputIndexLookahead.InputIndexLookaheadState → Nat
  | .scanIndex => 0
  | .peekTail => 1
  | .peekFrame => 2
  | .backSeparator .sourceTail => 3
  | .backSeparator .frameStack => 4
  | .backSeparator .done => 5
  | .rewind .sourceTail => 6
  | .rewind .frameStack => 7
  | .rewind .done => 8
  | .halt .sourceTail => 9
  | .halt .frameStack => 10
  | .halt .done => 11
  | .reject => 12

def lookaheadDecode : Nat → P01InputIndexLookahead.InputIndexLookaheadState
  | 0 => .scanIndex
  | 1 => .peekTail
  | 2 => .peekFrame
  | 3 => .backSeparator .sourceTail
  | 4 => .backSeparator .frameStack
  | 5 => .backSeparator .done
  | 6 => .rewind .sourceTail
  | 7 => .rewind .frameStack
  | 8 => .rewind .done
  | 9 => .halt .sourceTail
  | 10 => .halt .frameStack
  | 11 => .halt .done
  | _ => .reject

@[simp] theorem lookaheadDecode_code
    (q : P01InputIndexLookahead.InputIndexLookaheadState) :
    lookaheadDecode (lookaheadCode q) = q := by
  cases q with
  | scanIndex => rfl
  | peekTail => rfl
  | peekFrame => rfl
  | backSeparator m => cases m <;> rfl
  | rewind m => cases m <;> rfl
  | halt m => cases m <;> rfl
  | reject => rfl

theorem lookaheadCode_lt
    (q : P01InputIndexLookahead.InputIndexLookaheadState) :
    lookaheadCode q < 13 := by
  cases q with
  | scanIndex => decide
  | peekTail => decide
  | peekFrame => decide
  | backSeparator m => cases m <;> decide
  | rewind m => cases m <;> decide
  | halt m => cases m <;> decide
  | reject => decide

def preservingCode : P01WitnessIndexedReadPreserving.PreservingReadState → Nat
  | .indexNoMoved => 0
  | .indexMoved => 1
  | .advanceSep => 2
  | .seekMoved => 3
  | .scanMoved => 4
  | .capture => 5
  | .writeMoved false => 6
  | .writeMoved true => 7
  | .returnMoved => 8
  | .returnBlanks => 9
  | .finalSepNoMoved => 10
  | .finalReadNoMoved => 11
  | .finalSeekMoved => 12
  | .finalScanMoved => 13
  | .finalReadMoved => 14
  | .restoreStart false => 15
  | .restoreStart true => 16
  | .restoreInspect false => 17
  | .restoreInspect true => 18
  | .restoreWrite false false => 19
  | .restoreWrite false true => 20
  | .restoreWrite true false => 21
  | .restoreWrite true true => 22
  | .restoreHalt false => 23
  | .restoreHalt true => 24
  | .halt false => 25
  | .halt true => 26
  | .reject => 27

def preservingDecode : Nat → P01WitnessIndexedReadPreserving.PreservingReadState
  | 0 => .indexNoMoved
  | 1 => .indexMoved
  | 2 => .advanceSep
  | 3 => .seekMoved
  | 4 => .scanMoved
  | 5 => .capture
  | 6 => .writeMoved false
  | 7 => .writeMoved true
  | 8 => .returnMoved
  | 9 => .returnBlanks
  | 10 => .finalSepNoMoved
  | 11 => .finalReadNoMoved
  | 12 => .finalSeekMoved
  | 13 => .finalScanMoved
  | 14 => .finalReadMoved
  | 15 => .restoreStart false
  | 16 => .restoreStart true
  | 17 => .restoreInspect false
  | 18 => .restoreInspect true
  | 19 => .restoreWrite false false
  | 20 => .restoreWrite false true
  | 21 => .restoreWrite true false
  | 22 => .restoreWrite true true
  | 23 => .restoreHalt false
  | 24 => .restoreHalt true
  | 25 => .halt false
  | 26 => .halt true
  | _ => .reject

@[simp] theorem preservingDecode_code
    (q : P01WitnessIndexedReadPreserving.PreservingReadState) :
    preservingDecode (preservingCode q) = q := by
  cases q with
  | indexNoMoved => rfl
  | indexMoved => rfl
  | advanceSep => rfl
  | seekMoved => rfl
  | scanMoved => rfl
  | capture => rfl
  | writeMoved b => cases b <;> rfl
  | returnMoved => rfl
  | returnBlanks => rfl
  | finalSepNoMoved => rfl
  | finalReadNoMoved => rfl
  | finalSeekMoved => rfl
  | finalScanMoved => rfl
  | finalReadMoved => rfl
  | restoreStart b => cases b <;> rfl
  | restoreInspect b => cases b <;> rfl
  | restoreWrite b c => cases b <;> cases c <;> rfl
  | restoreHalt b => cases b <;> rfl
  | halt b => cases b <;> rfl
  | reject => rfl

theorem preservingCode_lt
    (q : P01WitnessIndexedReadPreserving.PreservingReadState) :
    preservingCode q < 28 := by
  cases q with
  | indexNoMoved => decide
  | indexMoved => decide
  | advanceSep => decide
  | seekMoved => decide
  | scanMoved => decide
  | capture => decide
  | writeMoved b => cases b <;> decide
  | returnMoved => decide
  | returnBlanks => decide
  | finalSepNoMoved => decide
  | finalReadNoMoved => decide
  | finalSeekMoved => decide
  | finalScanMoved => decide
  | finalReadMoved => decide
  | restoreStart b => cases b <;> decide
  | restoreInspect b => cases b <;> decide
  | restoreWrite b c => cases b <;> cases c <;> decide
  | restoreHalt b => cases b <;> decide
  | halt b => cases b <;> decide
  | reject => decide

def afterReadCode : P01InputAfterReadReturn.InputAfterReadReturnState → Nat
  | .start .sourceTail => 0
  | .start .frameStack => 1
  | .start .done => 2
  | .seekSource => 3
  | .scanSource => 4
  | .seekFrames => 5
  | .scanFrames => 6
  | .halt .sourceTail => 7
  | .halt .frameStack => 8
  | .halt .done => 9
  | .reject => 10

def afterReadDecode : Nat → P01InputAfterReadReturn.InputAfterReadReturnState
  | 0 => .start .sourceTail
  | 1 => .start .frameStack
  | 2 => .start .done
  | 3 => .seekSource
  | 4 => .scanSource
  | 5 => .seekFrames
  | 6 => .scanFrames
  | 7 => .halt .sourceTail
  | 8 => .halt .frameStack
  | 9 => .halt .done
  | _ => .reject

@[simp] theorem afterReadDecode_code
    (q : P01InputAfterReadReturn.InputAfterReadReturnState) :
    afterReadDecode (afterReadCode q) = q := by
  cases q with
  | start m => cases m <;> rfl
  | seekSource => rfl
  | scanSource => rfl
  | seekFrames => rfl
  | scanFrames => rfl
  | halt m => cases m <;> rfl
  | reject => rfl

theorem afterReadCode_lt
    (q : P01InputAfterReadReturn.InputAfterReadReturnState) :
    afterReadCode q < 11 := by
  cases q with
  | start m => cases m <;> decide
  | seekSource => decide
  | scanSource => decide
  | seekFrames => decide
  | scanFrames => decide
  | halt m => cases m <;> decide
  | reject => decide

def inputNodeStateCount : Nat := 170

def inputNodeCode : P01InputNodeCompositeNTM.InputNodeCompositeState → Nat
  | .look q => lookaheadCode q
  | .read .sourceTail q => 13 + preservingCode q
  | .read .frameStack q => 41 + preservingCode q
  | .read .done q => 69 + preservingCode q
  | .ret .sourceTail false q => 97 + afterReadCode q
  | .ret .sourceTail true q => 108 + afterReadCode q
  | .ret .frameStack false q => 119 + afterReadCode q
  | .ret .frameStack true q => 130 + afterReadCode q
  | .ret .done false q => 141 + afterReadCode q
  | .ret .done true q => 152 + afterReadCode q
  | .done false .sourceTail => 163
  | .done false .frameStack => 164
  | .done false .done => 165
  | .done true .sourceTail => 166
  | .done true .frameStack => 167
  | .done true .done => 168
  | .reject => 169

def inputNodeDecode (n : Nat) : P01InputNodeCompositeNTM.InputNodeCompositeState :=
  if n < 13 then .look (lookaheadDecode n)
  else if n < 41 then .read .sourceTail (preservingDecode (n - 13))
  else if n < 69 then .read .frameStack (preservingDecode (n - 41))
  else if n < 97 then .read .done (preservingDecode (n - 69))
  else if n < 108 then .ret .sourceTail false (afterReadDecode (n - 97))
  else if n < 119 then .ret .sourceTail true (afterReadDecode (n - 108))
  else if n < 130 then .ret .frameStack false (afterReadDecode (n - 119))
  else if n < 141 then .ret .frameStack true (afterReadDecode (n - 130))
  else if n < 152 then .ret .done false (afterReadDecode (n - 141))
  else if n < 163 then .ret .done true (afterReadDecode (n - 152))
  else if n = 163 then .done false .sourceTail
  else if n = 164 then .done false .frameStack
  else if n = 165 then .done false .done
  else if n = 166 then .done true .sourceTail
  else if n = 167 then .done true .frameStack
  else if n = 168 then .done true .done
  else .reject

@[simp] theorem inputNodeDecode_code
    (q : P01InputNodeCompositeNTM.InputNodeCompositeState) :
    inputNodeDecode (inputNodeCode q) = q := by
  cases q with
  | look q =>
      have h := lookaheadCode_lt q
      simp [inputNodeDecode, inputNodeCode, h, lookaheadDecode_code]
  | read m q =>
      have h := preservingCode_lt q
      cases m with
      | sourceTail =>
          have h13 : ¬ 13 + preservingCode q < 13 := by omega
          have h41 : 13 + preservingCode q < 41 := by omega
          have hsub : 13 + preservingCode q - 13 = preservingCode q := by omega
          simp [inputNodeDecode, inputNodeCode, h13, h41, hsub, preservingDecode_code]
      | frameStack =>
          have h13 : ¬ 41 + preservingCode q < 13 := by omega
          have h41 : ¬ 41 + preservingCode q < 41 := by omega
          have h69 : 41 + preservingCode q < 69 := by omega
          have hsub : 41 + preservingCode q - 41 = preservingCode q := by omega
          simp [inputNodeDecode, inputNodeCode, h13, h41, h69, hsub, preservingDecode_code]
      | done =>
          have h13 : ¬ 69 + preservingCode q < 13 := by omega
          have h41 : ¬ 69 + preservingCode q < 41 := by omega
          have h69 : ¬ 69 + preservingCode q < 69 := by omega
          have h97 : 69 + preservingCode q < 97 := by omega
          have hsub : 69 + preservingCode q - 69 = preservingCode q := by omega
          simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, hsub, preservingDecode_code]
  | ret m b q =>
      have h := afterReadCode_lt q
      cases m with
      | sourceTail =>
          cases b with
          | false =>
              have h13 : ¬ 97 + afterReadCode q < 13 := by omega
              have h41 : ¬ 97 + afterReadCode q < 41 := by omega
              have h69 : ¬ 97 + afterReadCode q < 69 := by omega
              have h97 : ¬ 97 + afterReadCode q < 97 := by omega
              have h108 : 97 + afterReadCode q < 108 := by omega
              have hsub : 97 + afterReadCode q - 97 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, hsub,
                afterReadDecode_code]
          | true =>
              have h13 : ¬ 108 + afterReadCode q < 13 := by omega
              have h41 : ¬ 108 + afterReadCode q < 41 := by omega
              have h69 : ¬ 108 + afterReadCode q < 69 := by omega
              have h97 : ¬ 108 + afterReadCode q < 97 := by omega
              have h108 : ¬ 108 + afterReadCode q < 108 := by omega
              have h119 : 108 + afterReadCode q < 119 := by omega
              have hsub : 108 + afterReadCode q - 108 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, h119, hsub,
                afterReadDecode_code]
      | frameStack =>
          cases b with
          | false =>
              have h13 : ¬ 119 + afterReadCode q < 13 := by omega
              have h41 : ¬ 119 + afterReadCode q < 41 := by omega
              have h69 : ¬ 119 + afterReadCode q < 69 := by omega
              have h97 : ¬ 119 + afterReadCode q < 97 := by omega
              have h108 : ¬ 119 + afterReadCode q < 108 := by omega
              have h119 : ¬ 119 + afterReadCode q < 119 := by omega
              have h130 : 119 + afterReadCode q < 130 := by omega
              have hsub : 119 + afterReadCode q - 119 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, h119, h130,
                hsub, afterReadDecode_code]
          | true =>
              have h13 : ¬ 130 + afterReadCode q < 13 := by omega
              have h41 : ¬ 130 + afterReadCode q < 41 := by omega
              have h69 : ¬ 130 + afterReadCode q < 69 := by omega
              have h97 : ¬ 130 + afterReadCode q < 97 := by omega
              have h108 : ¬ 130 + afterReadCode q < 108 := by omega
              have h119 : ¬ 130 + afterReadCode q < 119 := by omega
              have h130 : ¬ 130 + afterReadCode q < 130 := by omega
              have h141 : 130 + afterReadCode q < 141 := by omega
              have hsub : 130 + afterReadCode q - 130 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, h119, h130,
                h141, hsub, afterReadDecode_code]
      | done =>
          cases b with
          | false =>
              have h13 : ¬ 141 + afterReadCode q < 13 := by omega
              have h41 : ¬ 141 + afterReadCode q < 41 := by omega
              have h69 : ¬ 141 + afterReadCode q < 69 := by omega
              have h97 : ¬ 141 + afterReadCode q < 97 := by omega
              have h108 : ¬ 141 + afterReadCode q < 108 := by omega
              have h119 : ¬ 141 + afterReadCode q < 119 := by omega
              have h130 : ¬ 141 + afterReadCode q < 130 := by omega
              have h141 : ¬ 141 + afterReadCode q < 141 := by omega
              have h152 : 141 + afterReadCode q < 152 := by omega
              have hsub : 141 + afterReadCode q - 141 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, h119, h130,
                h141, h152, hsub, afterReadDecode_code]
          | true =>
              have h13 : ¬ 152 + afterReadCode q < 13 := by omega
              have h41 : ¬ 152 + afterReadCode q < 41 := by omega
              have h69 : ¬ 152 + afterReadCode q < 69 := by omega
              have h97 : ¬ 152 + afterReadCode q < 97 := by omega
              have h108 : ¬ 152 + afterReadCode q < 108 := by omega
              have h119 : ¬ 152 + afterReadCode q < 119 := by omega
              have h130 : ¬ 152 + afterReadCode q < 130 := by omega
              have h141 : ¬ 152 + afterReadCode q < 141 := by omega
              have h152 : ¬ 152 + afterReadCode q < 152 := by omega
              have h163 : 152 + afterReadCode q < 163 := by omega
              have hsub : 152 + afterReadCode q - 152 = afterReadCode q := by omega
              simp [inputNodeDecode, inputNodeCode, h13, h41, h69, h97, h108, h119, h130,
                h141, h152, h163, hsub, afterReadDecode_code]
    | done b m =>
      cases b <;> cases m <;> simp [inputNodeDecode, inputNodeCode]
  | reject =>
      simp [inputNodeDecode, inputNodeCode]

theorem inputNodeCode_lt
    (q : P01InputNodeCompositeNTM.InputNodeCompositeState) :
    inputNodeCode q < inputNodeStateCount := by
  cases q with
  | look q =>
      have h := lookaheadCode_lt q
      simp [inputNodeCode, inputNodeStateCount]
      omega
  | read m q =>
      have h := preservingCode_lt q
      cases m <;> simp [inputNodeCode, inputNodeStateCount] <;> omega
  | ret m b q =>
      have h := afterReadCode_lt q
      cases m <;> cases b <;>
        simp [inputNodeCode, inputNodeStateCount] <;> omega
  | done b m => cases b <;> cases m <;> decide
  | reject => decide

#print axioms MCore.Real.P01ManualStateCodecBase.inputNodeDecode_code

end P01ManualStateCodecBase
end Real
end MCore
