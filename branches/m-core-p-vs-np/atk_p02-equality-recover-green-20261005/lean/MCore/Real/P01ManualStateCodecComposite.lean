import MCore.Real.P01ManualStateCodecBase
import MCore.Real.P01CheckedVerifierCompositeNTM

set_option maxRecDepth 10000

namespace MCore
namespace Real
namespace P01ManualStateCodecComposite

open P01VerifierStateCode
open P01ManualStateCodecBase

def frameCursorCode
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) : Nat :=
  evalFrameCode f * 5 + cursorReturnCode q

def frameCursorDecode (n : Nat) :
    P01EncodedStackEvaluator.EvalFrame × P01EvalCursorRoundTrip.CursorReturnState :=
  if n < 5 then (.neg, cursorReturnDecode n)
  else if n < 10 then (.andLeft, cursorReturnDecode (n - 5))
  else if n < 15 then (.andRight false, cursorReturnDecode (n - 10))
  else if n < 20 then (.andRight true, cursorReturnDecode (n - 15))
  else if n < 25 then (.orLeft, cursorReturnDecode (n - 20))
  else if n < 30 then (.orRight false, cursorReturnDecode (n - 25))
  else (.orRight true, cursorReturnDecode (n - 30))

@[simp] theorem frameCursorDecode_code
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) :
    frameCursorDecode (frameCursorCode f q) = (f, q) := by
  cases f with
  | neg => cases q <;> rfl
  | andLeft => cases q <;> rfl
  | andRight b => cases b <;> cases q <;> rfl
  | orLeft => cases q <;> rfl
  | orRight b => cases b <;> cases q <;> rfl

theorem frameCursorCode_lt
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) :
    frameCursorCode f q < 35 := by
  cases f with
  | neg => cases q <;> decide
  | andLeft => cases q <;> decide
  | andRight b => cases b <;> cases q <;> decide
  | orLeft => cases q <;> decide
  | orRight b => cases b <;> cases q <;> decide

def framePushPairCode
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) : Nat :=
  evalFrameCode f * 23 + framePushCode q

def framePushPairDecode (n : Nat) :
    P01EncodedStackEvaluator.EvalFrame × P01EvalFramePushMachine.FramePushState :=
  if n < 23 then (.neg, framePushDecode n)
  else if n < 46 then (.andLeft, framePushDecode (n - 23))
  else if n < 69 then (.andRight false, framePushDecode (n - 46))
  else if n < 92 then (.andRight true, framePushDecode (n - 69))
  else if n < 115 then (.orLeft, framePushDecode (n - 92))
  else if n < 138 then (.orRight false, framePushDecode (n - 115))
  else (.orRight true, framePushDecode (n - 138))

@[simp] theorem framePushPairDecode_code
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) :
    framePushPairDecode (framePushPairCode f q) = (f, q) := by
  have h := framePushCode_lt q
  cases f with
  | neg =>
      have h23 : framePushCode q < 23 := h
      simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, framePushDecode_code]
  | andLeft =>
      have h23 : ¬ 23 + framePushCode q < 23 := by omega
      have h46 : 23 + framePushCode q < 46 := by omega
      have hsub : 23 + framePushCode q - 23 = framePushCode q := by omega
      simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, hsub,
        framePushDecode_code]
  | andRight b =>
      cases b with
      | false =>
          have h23 : ¬ 46 + framePushCode q < 23 := by omega
          have h46 : ¬ 46 + framePushCode q < 46 := by omega
          have h69 : 46 + framePushCode q < 69 := by omega
          have hsub : 46 + framePushCode q - 46 = framePushCode q := by omega
          simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, h69,
            hsub, framePushDecode_code]
      | true =>
          have h23 : ¬ 69 + framePushCode q < 23 := by omega
          have h46 : ¬ 69 + framePushCode q < 46 := by omega
          have h69 : ¬ 69 + framePushCode q < 69 := by omega
          have h92 : 69 + framePushCode q < 92 := by omega
          have hsub : 69 + framePushCode q - 69 = framePushCode q := by omega
          simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, h69,
            h92, hsub, framePushDecode_code]
  | orLeft =>
      have h23 : ¬ 92 + framePushCode q < 23 := by omega
      have h46 : ¬ 92 + framePushCode q < 46 := by omega
      have h69 : ¬ 92 + framePushCode q < 69 := by omega
      have h92 : ¬ 92 + framePushCode q < 92 := by omega
      have h115 : 92 + framePushCode q < 115 := by omega
      have hsub : 92 + framePushCode q - 92 = framePushCode q := by omega
      simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, h69,
        h92, h115, hsub, framePushDecode_code]
  | orRight b =>
      cases b with
      | false =>
          have h23 : ¬ 115 + framePushCode q < 23 := by omega
          have h46 : ¬ 115 + framePushCode q < 46 := by omega
          have h69 : ¬ 115 + framePushCode q < 69 := by omega
          have h92 : ¬ 115 + framePushCode q < 92 := by omega
          have h115 : ¬ 115 + framePushCode q < 115 := by omega
          have h138 : 115 + framePushCode q < 138 := by omega
          have hsub : 115 + framePushCode q - 115 = framePushCode q := by omega
          simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, h69,
            h92, h115, h138, hsub, framePushDecode_code]
      | true =>
          have h23 : ¬ 138 + framePushCode q < 23 := by omega
          have h46 : ¬ 138 + framePushCode q < 46 := by omega
          have h69 : ¬ 138 + framePushCode q < 69 := by omega
          have h92 : ¬ 138 + framePushCode q < 92 := by omega
          have h115 : ¬ 138 + framePushCode q < 115 := by omega
          have h138 : ¬ 138 + framePushCode q < 138 := by omega
          have hsub : 138 + framePushCode q - 138 = framePushCode q := by omega
          simp [framePushPairDecode, framePushPairCode, evalFrameCode, h23, h46, h69,
            h92, h115, h138, hsub, framePushDecode_code]

theorem framePushPairCode_lt
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) :
    framePushPairCode f q < 161 := by
  have h := framePushCode_lt q
  cases f with
  | neg => simp [framePushPairCode, evalFrameCode]; omega
  | andLeft => simp [framePushPairCode, evalFrameCode]; omega
  | andRight b => cases b <;> simp [framePushPairCode, evalFrameCode] <;> omega
  | orLeft => simp [framePushPairCode, evalFrameCode]; omega
  | orRight b => cases b <;> simp [framePushPairCode, evalFrameCode] <;> omega

def needExprStateCount : Nat := 401

def needExprCode : P01NeedExprCompositeNTM.NeedExprCompositeState → Nat
  | .seek q => cursorSeekCode q
  | .decode q => 5 + tagDecodeStateCode q
  | .input q => 21 + inputNodeCode q
  | .retValue false q => 191 + cursorReturnCode q
  | .retValue true q => 196 + cursorReturnCode q
  | .retPush f q => 201 + frameCursorCode f q
  | .push f q => 236 + framePushPairCode f q
  | .doneValue false => 397
  | .doneValue true => 398
  | .doneNeed => 399
  | .reject => 400

def needExprDecode (n : Nat) : P01NeedExprCompositeNTM.NeedExprCompositeState :=
  if n < 5 then .seek (cursorSeekDecode n)
  else if n < 21 then .decode (tagDecodeStateDecode (n - 5))
  else if n < 191 then .input (inputNodeDecode (n - 21))
  else if n < 196 then .retValue false (cursorReturnDecode (n - 191))
  else if n < 201 then .retValue true (cursorReturnDecode (n - 196))
  else if n < 236 then
    let p := frameCursorDecode (n - 201)
    .retPush p.1 p.2
  else if n < 397 then
    let p := framePushPairDecode (n - 236)
    .push p.1 p.2
  else if n = 397 then .doneValue false
  else if n = 398 then .doneValue true
  else if n = 399 then .doneNeed
  else .reject

@[simp] theorem needExprDecode_code
    (q : P01NeedExprCompositeNTM.NeedExprCompositeState) :
    needExprDecode (needExprCode q) = q := by
  cases q with
  | seek q =>
      have h := cursorSeekCode_lt q
      simp [needExprDecode, needExprCode, h, cursorSeekDecode_code]
  | decode q =>
      have h := tagDecodeStateCode_lt q
      have h5 : ¬ 5 + tagDecodeStateCode q < 5 := by omega
      have h21 : 5 + tagDecodeStateCode q < 21 := by omega
      have hsub : 5 + tagDecodeStateCode q - 5 = tagDecodeStateCode q := by omega
      simp [needExprDecode, needExprCode, h5, h21, hsub, tagDecodeStateDecode_code]
  | input q =>
      have h := inputNodeCode_lt q
      unfold inputNodeStateCount at h
      have h5 : ¬ 21 + inputNodeCode q < 5 := by omega
      have h21 : ¬ 21 + inputNodeCode q < 21 := by omega
      have h191 : 21 + inputNodeCode q < 191 := by omega
      have hsub : 21 + inputNodeCode q - 21 = inputNodeCode q := by omega
      simp [needExprDecode, needExprCode, h5, h21, h191, hsub, inputNodeDecode_code]
  | retValue b q =>
      have h := cursorReturnCode_lt q
      cases b with
      | false =>
          have h5 : ¬ 191 + cursorReturnCode q < 5 := by omega
          have h21 : ¬ 191 + cursorReturnCode q < 21 := by omega
          have h191 : ¬ 191 + cursorReturnCode q < 191 := by omega
          have h196 : 191 + cursorReturnCode q < 196 := by omega
          have hsub : 191 + cursorReturnCode q - 191 = cursorReturnCode q := by omega
          simp [needExprDecode, needExprCode, h5, h21, h191, h196, hsub,
            cursorReturnDecode_code]
      | true =>
          have h5 : ¬ 196 + cursorReturnCode q < 5 := by omega
          have h21 : ¬ 196 + cursorReturnCode q < 21 := by omega
          have h191 : ¬ 196 + cursorReturnCode q < 191 := by omega
          have h196 : ¬ 196 + cursorReturnCode q < 196 := by omega
          have h201 : 196 + cursorReturnCode q < 201 := by omega
          have hsub : 196 + cursorReturnCode q - 196 = cursorReturnCode q := by omega
          simp [needExprDecode, needExprCode, h5, h21, h191, h196, h201, hsub,
            cursorReturnDecode_code]
  | retPush f q =>
      have h := frameCursorCode_lt f q
      have h5 : ¬ 201 + frameCursorCode f q < 5 := by omega
      have h21 : ¬ 201 + frameCursorCode f q < 21 := by omega
      have h191 : ¬ 201 + frameCursorCode f q < 191 := by omega
      have h196 : ¬ 201 + frameCursorCode f q < 196 := by omega
      have h201 : ¬ 201 + frameCursorCode f q < 201 := by omega
      have h236 : 201 + frameCursorCode f q < 236 := by omega
      have hsub : 201 + frameCursorCode f q - 201 = frameCursorCode f q := by omega
      simp [needExprDecode, needExprCode, h5, h21, h191, h196, h201, h236, hsub,
        frameCursorDecode_code]
  | push f q =>
      have h := framePushPairCode_lt f q
      have h5 : ¬ 236 + framePushPairCode f q < 5 := by omega
      have h21 : ¬ 236 + framePushPairCode f q < 21 := by omega
      have h191 : ¬ 236 + framePushPairCode f q < 191 := by omega
      have h196 : ¬ 236 + framePushPairCode f q < 196 := by omega
      have h201 : ¬ 236 + framePushPairCode f q < 201 := by omega
      have h236 : ¬ 236 + framePushPairCode f q < 236 := by omega
      have h397 : 236 + framePushPairCode f q < 397 := by omega
      have hsub : 236 + framePushPairCode f q - 236 = framePushPairCode f q := by omega
      simp [needExprDecode, needExprCode, h5, h21, h191, h196, h201, h236, h397, hsub,
        framePushPairDecode_code]
  | doneValue b => cases b <;> simp [needExprDecode, needExprCode]
  | doneNeed => simp [needExprDecode, needExprCode]
  | reject => simp [needExprDecode, needExprCode]

theorem needExprCode_lt
    (q : P01NeedExprCompositeNTM.NeedExprCompositeState) :
    needExprCode q < needExprStateCount := by
  cases q with
  | seek q =>
      have h := cursorSeekCode_lt q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | decode q =>
      have h := tagDecodeStateCode_lt q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | input q =>
      have h := inputNodeCode_lt q
      unfold inputNodeStateCount at h
      simp [needExprCode, needExprStateCount]
      omega
  | retValue b q =>
      have h := cursorReturnCode_lt q
      cases b <;> simp [needExprCode, needExprStateCount, inputNodeStateCount] <;> omega
  | retPush f q =>
      have h := frameCursorCode_lt f q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | doneValue b => cases b <;> decide
  | doneNeed => decide
  | reject => decide

def haveValueStateCount : Nat := 213

def haveValueCode : P01HaveValueCompositeNTM.HaveValueCompositeState → Nat
  | .start false => 0
  | .start true => 1
  | .peek false => 2
  | .peek true => 3
  | .pop false q => 4 + framePopCode q
  | .pop true q => 26 + framePopCode q
  | .push f q => 48 + framePushPairCode f q
  | .doneValue false => 209
  | .doneValue true => 210
  | .doneNeed => 211
  | .reject => 212

def haveValueDecode (n : Nat) : P01HaveValueCompositeNTM.HaveValueCompositeState :=
  if n = 0 then .start false
  else if n = 1 then .start true
  else if n = 2 then .peek false
  else if n = 3 then .peek true
  else if n < 26 then .pop false (framePopDecode (n - 4))
  else if n < 48 then .pop true (framePopDecode (n - 26))
  else if n < 209 then
    let p := framePushPairDecode (n - 48)
    .push p.1 p.2
  else if n = 209 then .doneValue false
  else if n = 210 then .doneValue true
  else if n = 211 then .doneNeed
  else .reject

@[simp] theorem haveValueDecode_code
    (q : P01HaveValueCompositeNTM.HaveValueCompositeState) :
    haveValueDecode (haveValueCode q) = q := by
  cases q with
  | start b => cases b <;> simp [haveValueDecode, haveValueCode]
  | peek b => cases b <;> simp [haveValueDecode, haveValueCode]
  | pop b q =>
      have h := framePopCode_lt q
      cases b with
      | false =>
          have h0 : 4 + framePopCode q ≠ 0 := by omega
          have h1 : 4 + framePopCode q ≠ 1 := by omega
          have h2 : 4 + framePopCode q ≠ 2 := by omega
          have h3 : 4 + framePopCode q ≠ 3 := by omega
          have h26 : 4 + framePopCode q < 26 := by omega
          have hsub : 4 + framePopCode q - 4 = framePopCode q := by omega
          simp [haveValueDecode, haveValueCode, h0, h1, h2, h3, h26, hsub,
            framePopDecode_code]
      | true =>
          have h0 : 26 + framePopCode q ≠ 0 := by omega
          have h1 : 26 + framePopCode q ≠ 1 := by omega
          have h2 : 26 + framePopCode q ≠ 2 := by omega
          have h3 : 26 + framePopCode q ≠ 3 := by omega
          have h26 : ¬ 26 + framePopCode q < 26 := by omega
          have h48 : 26 + framePopCode q < 48 := by omega
          have hsub : 26 + framePopCode q - 26 = framePopCode q := by omega
          simp [haveValueDecode, haveValueCode, h0, h1, h2, h3, h26, h48, hsub,
            framePopDecode_code]
  | push f q =>
      have h := framePushPairCode_lt f q
      have h0 : 48 + framePushPairCode f q ≠ 0 := by omega
      have h1 : 48 + framePushPairCode f q ≠ 1 := by omega
      have h2 : 48 + framePushPairCode f q ≠ 2 := by omega
      have h3 : 48 + framePushPairCode f q ≠ 3 := by omega
      have h26 : ¬ 48 + framePushPairCode f q < 26 := by omega
      have h48 : ¬ 48 + framePushPairCode f q < 48 := by omega
      have h209 : 48 + framePushPairCode f q < 209 := by omega
      have hsub : 48 + framePushPairCode f q - 48 = framePushPairCode f q := by omega
      simp [haveValueDecode, haveValueCode, h0, h1, h2, h3, h26, h48, h209, hsub,
        framePushPairDecode_code]
  | doneValue b => cases b <;> simp [haveValueDecode, haveValueCode]
  | doneNeed => simp [haveValueDecode, haveValueCode]
  | reject => simp [haveValueDecode, haveValueCode]

theorem haveValueCode_lt
    (q : P01HaveValueCompositeNTM.HaveValueCompositeState) :
    haveValueCode q < haveValueStateCount := by
  cases q with
  | start b => cases b <;> decide
  | peek b => cases b <;> decide
  | pop b q =>
      have h := framePopCode_lt q
      cases b <;> simp [haveValueCode, haveValueStateCount] <;> omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [haveValueCode, haveValueStateCount]
      omega
  | doneValue b => cases b <;> decide
  | doneNeed => decide
  | reject => decide

def checkedEvalStateCount : Nat := 1847

def checkedEvalCode : P01CheckedEvalRunLoopNTM.CheckedEvalRunState → Nat
  | .need .cnf q => needExprCode q
  | .need .clause q => 401 + needExprCode q
  | .need .mustInput q => 802 + needExprCode q
  | .have .cnf q => 1203 + haveValueCode q
  | .have .clause q => 1416 + haveValueCode q
  | .have .mustInput q => 1629 + haveValueCode q
  | .checkSource false => 1842
  | .checkSource true => 1843
  | .final false => 1844
  | .final true => 1845
  | .reject => 1846

def checkedEvalDecode (n : Nat) : P01CheckedEvalRunLoopNTM.CheckedEvalRunState :=
  if n < 401 then .need .cnf (needExprDecode n)
  else if n < 802 then .need .clause (needExprDecode (n - 401))
  else if n < 1203 then .need .mustInput (needExprDecode (n - 802))
  else if n < 1416 then .have .cnf (haveValueDecode (n - 1203))
  else if n < 1629 then .have .clause (haveValueDecode (n - 1416))
  else if n < 1842 then .have .mustInput (haveValueDecode (n - 1629))
  else if n = 1842 then .checkSource false
  else if n = 1843 then .checkSource true
  else if n = 1844 then .final false
  else if n = 1845 then .final true
  else .reject

@[simp] theorem checkedEvalDecode_code
    (q : P01CheckedEvalRunLoopNTM.CheckedEvalRunState) :
    checkedEvalDecode (checkedEvalCode q) = q := by
  cases q with
  | need m q =>
      have h := needExprCode_lt q
      unfold needExprStateCount at h
      cases m with
      | cnf =>
          have h401 : needExprCode q < 401 := h
          simp [checkedEvalDecode, checkedEvalCode, h401, needExprDecode_code]
      | clause =>
          have h401 : ¬ 401 + needExprCode q < 401 := by omega
          have h802 : 401 + needExprCode q < 802 := by omega
          have hsub : 401 + needExprCode q - 401 = needExprCode q := by omega
          simp [checkedEvalDecode, checkedEvalCode, h401, h802, hsub, needExprDecode_code]
      | mustInput =>
          have h401 : ¬ 802 + needExprCode q < 401 := by omega
          have h802 : ¬ 802 + needExprCode q < 802 := by omega
          have h1203 : 802 + needExprCode q < 1203 := by omega
          have hsub : 802 + needExprCode q - 802 = needExprCode q := by omega
          simp [checkedEvalDecode, checkedEvalCode, h401, h802, h1203, hsub,
            needExprDecode_code]
  | «have» m q =>
      have h := haveValueCode_lt q
      unfold haveValueStateCount at h
      cases m with
      | cnf =>
          have h401 : ¬ 1203 + haveValueCode q < 401 := by omega
          have h802 : ¬ 1203 + haveValueCode q < 802 := by omega
          have h1203 : ¬ 1203 + haveValueCode q < 1203 := by omega
          have h1416 : 1203 + haveValueCode q < 1416 := by omega
          have hsub : 1203 + haveValueCode q - 1203 = haveValueCode q := by omega
          simp [checkedEvalDecode, checkedEvalCode, h401, h802, h1203, h1416, hsub,
            haveValueDecode_code]
      | clause =>
          have h401 : ¬ 1416 + haveValueCode q < 401 := by omega
          have h802 : ¬ 1416 + haveValueCode q < 802 := by omega
          have h1203 : ¬ 1416 + haveValueCode q < 1203 := by omega
          have h1416 : ¬ 1416 + haveValueCode q < 1416 := by omega
          have h1629 : 1416 + haveValueCode q < 1629 := by omega
          have hsub : 1416 + haveValueCode q - 1416 = haveValueCode q := by omega
          simp [checkedEvalDecode, checkedEvalCode, h401, h802, h1203, h1416, h1629,
            hsub, haveValueDecode_code]
      | mustInput =>
          have h401 : ¬ 1629 + haveValueCode q < 401 := by omega
          have h802 : ¬ 1629 + haveValueCode q < 802 := by omega
          have h1203 : ¬ 1629 + haveValueCode q < 1203 := by omega
          have h1416 : ¬ 1629 + haveValueCode q < 1416 := by omega
          have h1629 : ¬ 1629 + haveValueCode q < 1629 := by omega
          have h1842 : 1629 + haveValueCode q < 1842 := by omega
          have hsub : 1629 + haveValueCode q - 1629 = haveValueCode q := by omega
          simp [checkedEvalDecode, checkedEvalCode, h401, h802, h1203, h1416, h1629,
            h1842, hsub, haveValueDecode_code]
  | checkSource b => cases b <;> simp [checkedEvalDecode, checkedEvalCode]
  | final b => cases b <;> simp [checkedEvalDecode, checkedEvalCode]
  | reject => simp [checkedEvalDecode, checkedEvalCode]

theorem checkedEvalCode_lt
    (q : P01CheckedEvalRunLoopNTM.CheckedEvalRunState) :
    checkedEvalCode q < checkedEvalStateCount := by
  cases q with
  | need m q =>
      have h := needExprCode_lt q
      unfold needExprStateCount at h
      cases m with
      | cnf =>
          unfold checkedEvalStateCount
          simpa [checkedEvalCode] using Nat.lt_trans h (by decide : 401 < 1847)
      | clause =>
          unfold checkedEvalStateCount
          have : 401 + needExprCode q < 802 := by omega
          exact Nat.lt_trans this (by decide : 802 < 1847)
      | mustInput =>
          unfold checkedEvalStateCount
          have : 802 + needExprCode q < 1203 := by omega
          exact Nat.lt_trans this (by decide : 1203 < 1847)
  | «have» m q =>
      have h := haveValueCode_lt q
      unfold haveValueStateCount at h
      cases m with
      | cnf =>
          unfold checkedEvalStateCount
          have : 1203 + haveValueCode q < 1416 := by omega
          exact Nat.lt_trans this (by decide : 1416 < 1847)
      | clause =>
          unfold checkedEvalStateCount
          have : 1416 + haveValueCode q < 1629 := by omega
          exact Nat.lt_trans this (by decide : 1629 < 1847)
      | mustInput =>
          unfold checkedEvalStateCount
          have : 1629 + haveValueCode q < 1842 := by omega
          exact Nat.lt_trans this (by decide : 1842 < 1847)
  | checkSource b => cases b <;> decide
  | final b => cases b <;> decide
  | reject => decide

#print axioms MCore.Real.P01ManualStateCodecComposite.needExprDecode_code
#print axioms MCore.Real.P01ManualStateCodecComposite.haveValueDecode_code
#print axioms MCore.Real.P01ManualStateCodecComposite.checkedEvalDecode_code

end P01ManualStateCodecComposite
end Real
end MCore
