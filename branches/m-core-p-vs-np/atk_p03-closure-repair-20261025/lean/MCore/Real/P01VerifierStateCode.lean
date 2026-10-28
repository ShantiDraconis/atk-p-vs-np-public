import MCore.Real.P01VerifierEvalCompositeNTM

namespace MCore
namespace Real
namespace P01VerifierStateCode

open P01EncodedStackEvaluator
open P01InputReturnMode
open P01InputIndexLookahead
open P01WitnessIndexedReadPreserving
open P01InputAfterReadReturn
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprTagDecode
open P01EvalFramePushMachine
open P01EvalFramePopMachineV2

def boolCode : Bool → Nat
  | false => 0
  | true => 1

def boolDecode : Nat → Bool
  | 0 => false
  | _ => true

@[simp] theorem boolDecode_code (b : Bool) :
    boolDecode (boolCode b) = b := by
  cases b <;> rfl

theorem boolCode_lt (b : Bool) : boolCode b < 2 := by
  cases b <;> decide

def evalFrameCode : EvalFrame → Nat
  | .neg => 0
  | .andLeft => 1
  | .andRight false => 2
  | .andRight true => 3
  | .orLeft => 4
  | .orRight false => 5
  | .orRight true => 6

def evalFrameDecode : Nat → EvalFrame
  | 0 => .neg
  | 1 => .andLeft
  | 2 => .andRight false
  | 3 => .andRight true
  | 4 => .orLeft
  | 5 => .orRight false
  | _ => .orRight true

@[simp] theorem evalFrameDecode_code (f : EvalFrame) :
    evalFrameDecode (evalFrameCode f) = f := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

theorem evalFrameCode_lt (f : EvalFrame) : evalFrameCode f < 7 := by
  cases f with
  | neg => decide
  | andLeft => decide
  | andRight b => cases b <;> decide
  | orLeft => decide
  | orRight b => cases b <;> decide

def returnModeCode : InputReturnMode → Nat
  | .sourceTail => 0
  | .frameStack => 1
  | .done => 2

def returnModeDecode : Nat → InputReturnMode
  | 0 => .sourceTail
  | 1 => .frameStack
  | _ => .done

@[simp] theorem returnModeDecode_code (m : InputReturnMode) :
    returnModeDecode (returnModeCode m) = m := by
  cases m <;> rfl

theorem returnModeCode_lt (m : InputReturnMode) :
    returnModeCode m < 3 := by
  cases m <;> decide

def cursorSeekCode : CursorSeekState → Nat
  | .start => 0
  | .scanStack => 1
  | .scanUnread => 2
  | .halt => 3
  | .reject => 4

def cursorSeekDecode : Nat → CursorSeekState
  | 0 => .start
  | 1 => .scanStack
  | 2 => .scanUnread
  | 3 => .halt
  | _ => .reject

@[simp] theorem cursorSeekDecode_code (q : CursorSeekState) :
    cursorSeekDecode (cursorSeekCode q) = q := by
  cases q <;> rfl

theorem cursorSeekCode_lt (q : CursorSeekState) :
    cursorSeekCode q < 5 := by
  cases q <;> decide

def cursorReturnCode : CursorReturnState → Nat
  | .erase => 0
  | .scanUnread => 1
  | .scanFrames => 2
  | .halt => 3
  | .reject => 4

def cursorReturnDecode : Nat → CursorReturnState
  | 0 => .erase
  | 1 => .scanUnread
  | 2 => .scanFrames
  | 3 => .halt
  | _ => .reject

@[simp] theorem cursorReturnDecode_code (q : CursorReturnState) :
    cursorReturnDecode (cursorReturnCode q) = q := by
  cases q <;> rfl

theorem cursorReturnCode_lt (q : CursorReturnState) :
    cursorReturnCode q < 5 := by
  cases q <;> decide

def needTagCode : NeedExprTag → Nat
  | .input => 0
  | .constFalse => 1
  | .constTrue => 2
  | .neg => 3
  | .and => 4
  | .or => 5
  | .invalid110 => 6
  | .invalid111 => 7

def needTagDecode : Nat → NeedExprTag
  | 0 => .input
  | 1 => .constFalse
  | 2 => .constTrue
  | 3 => .neg
  | 4 => .and
  | 5 => .or
  | 6 => .invalid110
  | _ => .invalid111

@[simp] theorem needTagDecode_code (t : NeedExprTag) :
    needTagDecode (needTagCode t) = t := by
  cases t <;> rfl

theorem needTagCode_lt (t : NeedExprTag) : needTagCode t < 8 := by
  cases t <;> decide

def tagDecodeStateCode : TagDecodeState → Nat
  | .start => 0
  | .bit1 false => 1
  | .bit1 true => 2
  | .bit2 false false => 3
  | .bit2 false true => 4
  | .bit2 true false => 5
  | .bit2 true true => 6
  | .halt t => 7 + needTagCode t
  | .reject => 15

def tagDecodeStateDecode : Nat → TagDecodeState
  | 0 => .start
  | 1 => .bit1 false
  | 2 => .bit1 true
  | 3 => .bit2 false false
  | 4 => .bit2 false true
  | 5 => .bit2 true false
  | 6 => .bit2 true true
  | 7 => .halt .input
  | 8 => .halt .constFalse
  | 9 => .halt .constTrue
  | 10 => .halt .neg
  | 11 => .halt .and
  | 12 => .halt .or
  | 13 => .halt .invalid110
  | 14 => .halt .invalid111
  | _ => .reject

@[simp] theorem tagDecodeStateDecode_code (q : TagDecodeState) :
    tagDecodeStateDecode (tagDecodeStateCode q) = q := by
  cases q with
  | start => rfl
  | bit1 b => cases b <;> rfl
  | bit2 b0 b1 => cases b0 <;> cases b1 <;> rfl
  | halt t => cases t <;> rfl
  | reject => rfl

theorem tagDecodeStateCode_lt (q : TagDecodeState) :
    tagDecodeStateCode q < 16 := by
  cases q with
  | start => decide
  | bit1 b => cases b <;> decide
  | bit2 b0 b1 => cases b0 <;> cases b1 <;> decide
  | halt t =>
      have h := needTagCode_lt t
      simp [tagDecodeStateCode]
      omega
  | reject => decide

def framePushCode : FramePushState → Nat
  | .start f => evalFrameCode f
  | .after1 f => 7 + evalFrameCode f
  | .after2 f => 14 + evalFrameCode f
  | .halt => 21
  | .reject => 22

def framePushDecode (n : Nat) : FramePushState :=
  if n < 7 then .start (evalFrameDecode n)
  else if n < 14 then .after1 (evalFrameDecode (n - 7))
  else if n < 21 then .after2 (evalFrameDecode (n - 14))
  else if n = 21 then .halt
  else .reject

@[simp] theorem framePushDecode_code (q : FramePushState) :
    framePushDecode (framePushCode q) = q := by
  cases q with
  | start f =>
      cases f with
      | neg => rfl
      | andLeft => rfl
      | andRight b => cases b <;> rfl
      | orLeft => rfl
      | orRight b => cases b <;> rfl
  | after1 f =>
      cases f with
      | neg => rfl
      | andLeft => rfl
      | andRight b => cases b <;> rfl
      | orLeft => rfl
      | orRight b => cases b <;> rfl
  | after2 f =>
      cases f with
      | neg => rfl
      | andLeft => rfl
      | andRight b => cases b <;> rfl
      | orLeft => rfl
      | orRight b => cases b <;> rfl
  | halt => rfl
  | reject => rfl

theorem framePushCode_lt (q : FramePushState) :
    framePushCode q < 23 := by
  cases q with
  | start f =>
      exact Nat.lt_trans (evalFrameCode_lt f) (by decide)
  | after1 f =>
      have h := evalFrameCode_lt f
      simp [framePushCode]
      omega
  | after2 f =>
      have h := evalFrameCode_lt f
      simp [framePushCode]
      omega
  | halt => decide
  | reject => decide

def framePopCode : FramePopState → Nat
  | .start => 0
  | .read0 => 1
  | .gap1 false => 2
  | .gap1 true => 3
  | .read1 false => 4
  | .read1 true => 5
  | .gap2 false false => 6
  | .gap2 false true => 7
  | .gap2 true false => 8
  | .gap2 true true => 9
  | .read2 false false => 10
  | .read2 false true => 11
  | .read2 true false => 12
  | .read2 true true => 13
  | .halt f => 14 + evalFrameCode f
  | .reject => 21

def framePopDecode : Nat → FramePopState
  | 0 => .start
  | 1 => .read0
  | 2 => .gap1 false
  | 3 => .gap1 true
  | 4 => .read1 false
  | 5 => .read1 true
  | 6 => .gap2 false false
  | 7 => .gap2 false true
  | 8 => .gap2 true false
  | 9 => .gap2 true true
  | 10 => .read2 false false
  | 11 => .read2 false true
  | 12 => .read2 true false
  | 13 => .read2 true true
  | 14 => .halt .neg
  | 15 => .halt .andLeft
  | 16 => .halt (.andRight false)
  | 17 => .halt (.andRight true)
  | 18 => .halt .orLeft
  | 19 => .halt (.orRight false)
  | 20 => .halt (.orRight true)
  | _ => .reject

@[simp] theorem framePopDecode_code (q : FramePopState) :
    framePopDecode (framePopCode q) = q := by
  cases q with
  | start => rfl
  | read0 => rfl
  | gap1 b => cases b <;> rfl
  | read1 b => cases b <;> rfl
  | gap2 b0 b1 => cases b0 <;> cases b1 <;> rfl
  | read2 b0 b1 => cases b0 <;> cases b1 <;> rfl
  | halt f =>
      cases f with
      | neg => rfl
      | andLeft => rfl
      | andRight b => cases b <;> rfl
      | orLeft => rfl
      | orRight b => cases b <;> rfl
  | reject => rfl

theorem framePopCode_lt (q : FramePopState) :
    framePopCode q < 22 := by
  cases q with
  | start => decide
  | read0 => decide
  | gap1 b => cases b <;> decide
  | read1 b => cases b <;> decide
  | gap2 b0 b1 => cases b0 <;> cases b1 <;> decide
  | read2 b0 b1 => cases b0 <;> cases b1 <;> decide
  | halt f =>
      have h := evalFrameCode_lt f
      simp [framePopCode]
      omega
  | reject => decide

#print axioms MCore.Real.P01VerifierStateCode.evalFrameDecode_code
#print axioms MCore.Real.P01VerifierStateCode.tagDecodeStateDecode_code
#print axioms MCore.Real.P01VerifierStateCode.framePushDecode_code
#print axioms MCore.Real.P01VerifierStateCode.framePopDecode_code

end P01VerifierStateCode
end Real
end MCore
