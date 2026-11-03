import MCore.Real.P01FiniteCodec
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01InputReturnMode
import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01WitnessIndexedReadPreserving
import MCore.Real.P01InputAfterReadReturn
import MCore.Real.P01InputNodeCompositeNTM
import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01EvalFramePopMachineV2
import MCore.Real.P01HaveValueCompositeNTM

namespace MCore
namespace Real
namespace P01CheckedVerifierStateCodec

open P01FiniteCodec
open P01EncodedStackEvaluator
open P01InputReturnMode
open P01InputIndexLookahead
open P01WitnessIndexedReadPreserving
open P01InputAfterReadReturn
open P01InputNodeCompositeNTM
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprTagDecode
open P01EvalFramePushMachine
open P01EvalFramePopMachineV2
open P01NeedExprCompositeNTM
open P01HaveValueCompositeNTM
open P01CNFMode
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM

/-! Primitive finite controls. -/

def evalFrameCodec : FinCodec EvalFrame :=
  mapCodec
    (sumCodec unitCodec
      (sumCodec unitCodec
        (sumCodec boolCodec
          (sumCodec unitCodec boolCodec))))
    (fun f =>
      match f with
      | .neg => Sum.inl ()
      | .andLeft => Sum.inr (Sum.inl ())
      | .andRight b => Sum.inr (Sum.inr (Sum.inl b))
      | .orLeft => Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
      | .orRight b => Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))
    (fun r =>
      match r with
      | .inl _ => .neg
      | .inr (.inl _) => .andLeft
      | .inr (.inr (.inl b)) => .andRight b
      | .inr (.inr (.inr (.inl _))) => .orLeft
      | .inr (.inr (.inr (.inr b))) => .orRight b)
    (by intro f; cases f <;> rfl)

theorem evalFrameCodec_size : evalFrameCodec.size = 7 := by rfl

def inputReturnModeCodec : FinCodec InputReturnMode where
  size := 3
  pos := by decide
  encode
    | .sourceTail => ⟨0, by decide⟩
    | .frameStack => ⟨1, by decide⟩
    | .done => ⟨2, by decide⟩
  decode := fun i =>
    match i.val with
    | 0 => .sourceTail
    | 1 => .frameStack
    | _ => .done
  decode_encode := by intro x; cases x <;> rfl

def inputReturnClassifyCodec : FinCodec InputReturnClassifyState :=
  mapCodec
    (sumCodec unitCodec
      (sumCodec unitCodec
        (sumCodec unitCodec
          (sumCodec inputReturnModeCodec
            (sumCodec inputReturnModeCodec unitCodec)))))
    (fun q =>
      match q with
      | .start => .inl ()
      | .peekTail => .inr (.inl ())
      | .peekFrame => .inr (.inr (.inl ()))
      | .backSeparator m => .inr (.inr (.inr (.inl m)))
      | .halt m => .inr (.inr (.inr (.inr (.inl m))))
      | .reject => .inr (.inr (.inr (.inr (.inr ())))))
    (fun r =>
      match r with
      | .inl _ => .start
      | .inr (.inl _) => .peekTail
      | .inr (.inr (.inl _)) => .peekFrame
      | .inr (.inr (.inr (.inl m))) => .backSeparator m
      | .inr (.inr (.inr (.inr (.inl m)))) => .halt m
      | .inr (.inr (.inr (.inr (.inr _)))) => .reject)
    (by intro q; cases q <;> rfl)

theorem inputReturnClassifyCodec_size :
    inputReturnClassifyCodec.size = 10 := by rfl

def inputIndexLookaheadCodec : FinCodec InputIndexLookaheadState :=
  mapCodec
    (sumCodec unitCodec
      (sumCodec unitCodec
        (sumCodec unitCodec
          (sumCodec inputReturnModeCodec
            (sumCodec inputReturnModeCodec
              (sumCodec inputReturnModeCodec unitCodec))))))
    (fun q =>
      match q with
      | .scanIndex => .inl ()
      | .peekTail => .inr (.inl ())
      | .peekFrame => .inr (.inr (.inl ()))
      | .backSeparator m => .inr (.inr (.inr (.inl m)))
      | .rewind m => .inr (.inr (.inr (.inr (.inl m))))
      | .halt m => .inr (.inr (.inr (.inr (.inr (.inl m)))))
      | .reject => .inr (.inr (.inr (.inr (.inr (.inr ()))))))
    (fun r =>
      match r with
      | .inl _ => .scanIndex
      | .inr (.inl _) => .peekTail
      | .inr (.inr (.inl _)) => .peekFrame
      | .inr (.inr (.inr (.inl m))) => .backSeparator m
      | .inr (.inr (.inr (.inr (.inl m)))) => .rewind m
      | .inr (.inr (.inr (.inr (.inr (.inl m))))) => .halt m
      | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .reject)
    (by intro q; cases q <;> rfl)

theorem inputIndexLookaheadCodec_size :
    inputIndexLookaheadCodec.size = 13 := by rfl

/-! The 28-state preserving witness reader is encoded explicitly. -/

def preservingReadEncode : PreservingReadState → Fin 28
  | .indexNoMoved => ⟨0, by decide⟩
  | .indexMoved => ⟨1, by decide⟩
  | .advanceSep => ⟨2, by decide⟩
  | .seekMoved => ⟨3, by decide⟩
  | .scanMoved => ⟨4, by decide⟩
  | .capture => ⟨5, by decide⟩
  | .writeMoved false => ⟨6, by decide⟩
  | .writeMoved true => ⟨7, by decide⟩
  | .returnMoved => ⟨8, by decide⟩
  | .returnBlanks => ⟨9, by decide⟩
  | .finalSepNoMoved => ⟨10, by decide⟩
  | .finalReadNoMoved => ⟨11, by decide⟩
  | .finalSeekMoved => ⟨12, by decide⟩
  | .finalScanMoved => ⟨13, by decide⟩
  | .finalReadMoved => ⟨14, by decide⟩
  | .restoreStart false => ⟨15, by decide⟩
  | .restoreStart true => ⟨16, by decide⟩
  | .restoreInspect false => ⟨17, by decide⟩
  | .restoreInspect true => ⟨18, by decide⟩
  | .restoreWrite false false => ⟨19, by decide⟩
  | .restoreWrite false true => ⟨20, by decide⟩
  | .restoreWrite true false => ⟨21, by decide⟩
  | .restoreWrite true true => ⟨22, by decide⟩
  | .restoreHalt false => ⟨23, by decide⟩
  | .restoreHalt true => ⟨24, by decide⟩
  | .halt false => ⟨25, by decide⟩
  | .halt true => ⟨26, by decide⟩
  | .reject => ⟨27, by decide⟩

def preservingReadDecode (i : Fin 28) : PreservingReadState :=
  match i.val with
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

theorem preservingReadDecode_encode (q : PreservingReadState) :
    preservingReadDecode (preservingReadEncode q) = q := by
  cases q <;> first | rfl | (rename_i b; cases b <;> rfl) |
    (rename_i a b; cases a <;> cases b <;> rfl)

def preservingReadCodec : FinCodec PreservingReadState where
  size := 28
  pos := by decide
  encode := preservingReadEncode
  decode := preservingReadDecode
  decode_encode := preservingReadDecode_encode

def inputAfterReadReturnCodec : FinCodec InputAfterReadReturnState :=
  mapCodec
    (sumCodec inputReturnModeCodec
      (sumCodec unitCodec
        (sumCodec unitCodec
          (sumCodec unitCodec
            (sumCodec unitCodec
              (sumCodec inputReturnModeCodec unitCodec))))))
    (fun q =>
      match q with
      | .start m => .inl m
      | .seekSource => .inr (.inl ())
      | .scanSource => .inr (.inr (.inl ()))
      | .seekFrames => .inr (.inr (.inr (.inl ())))
      | .scanFrames => .inr (.inr (.inr (.inr (.inl ()))))
      | .halt m => .inr (.inr (.inr (.inr (.inr (.inl m)))))
      | .reject => .inr (.inr (.inr (.inr (.inr (.inr ()))))))
    (fun r =>
      match r with
      | .inl m => .start m
      | .inr (.inl _) => .seekSource
      | .inr (.inr (.inl _)) => .scanSource
      | .inr (.inr (.inr (.inl _))) => .seekFrames
      | .inr (.inr (.inr (.inr (.inl _)))) => .scanFrames
      | .inr (.inr (.inr (.inr (.inr (.inl m))))) => .halt m
      | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .reject)
    (by intro q; cases q <;> rfl)

theorem inputAfterReadReturnCodec_size :
    inputAfterReadReturnCodec.size = 11 := by rfl

/-! Composite input-node control: 13 + 3*28 + 3*2*11 + 2*3 + 1 = 170. -/

abbrev InputNodeRep :=
  Sum InputIndexLookaheadState
    (Sum (InputReturnMode × PreservingReadState)
      (Sum (InputReturnMode × (Bool × InputAfterReadReturnState))
        (Sum (Bool × InputReturnMode) Unit)))

def inputNodeRepCodec : FinCodec InputNodeRep :=
  sumCodec inputIndexLookaheadCodec
    (sumCodec (prodCodec inputReturnModeCodec preservingReadCodec)
      (sumCodec
        (prodCodec inputReturnModeCodec
          (prodCodec boolCodec inputAfterReadReturnCodec))
        (sumCodec (prodCodec boolCodec inputReturnModeCodec) unitCodec)))

def inputNodeCompositeCodec : FinCodec InputNodeCompositeState :=
  mapCodec inputNodeRepCodec
    (fun q =>
      match q with
      | .look s => .inl s
      | .read m s => .inr (.inl (m,s))
      | .ret m b s => .inr (.inr (.inl (m,(b,s))))
      | .done b m => .inr (.inr (.inr (.inl (b,m))))
      | .reject => .inr (.inr (.inr (.inr ()))))
    (fun r =>
      match r with
      | .inl s => .look s
      | .inr (.inl (m,s)) => .read m s
      | .inr (.inr (.inl (m,(b,s)))) => .ret m b s
      | .inr (.inr (.inr (.inl (b,m)))) => .done b m
      | .inr (.inr (.inr (.inr _))) => .reject)
    (by intro q; cases q <;> rfl)

theorem inputNodeCompositeCodec_size :
    inputNodeCompositeCodec.size = 170 := by rfl

def cursorSeekCodec : FinCodec CursorSeekState where
  size := 5
  pos := by decide
  encode
    | .start => ⟨0, by decide⟩
    | .scanStack => ⟨1, by decide⟩
    | .scanUnread => ⟨2, by decide⟩
    | .halt => ⟨3, by decide⟩
    | .reject => ⟨4, by decide⟩
  decode := fun i =>
    match i.val with
    | 0 => .start | 1 => .scanStack | 2 => .scanUnread | 3 => .halt | _ => .reject
  decode_encode := by intro q; cases q <;> rfl

def cursorReturnCodec : FinCodec CursorReturnState where
  size := 5
  pos := by decide
  encode
    | .erase => ⟨0, by decide⟩
    | .scanUnread => ⟨1, by decide⟩
    | .scanFrames => ⟨2, by decide⟩
    | .halt => ⟨3, by decide⟩
    | .reject => ⟨4, by decide⟩
  decode := fun i =>
    match i.val with
    | 0 => .erase | 1 => .scanUnread | 2 => .scanFrames | 3 => .halt | _ => .reject
  decode_encode := by intro q; cases q <;> rfl

def needExprTagCodec : FinCodec NeedExprTag where
  size := 8
  pos := by decide
  encode
    | .input => ⟨0, by decide⟩
    | .constFalse => ⟨1, by decide⟩
    | .constTrue => ⟨2, by decide⟩
    | .neg => ⟨3, by decide⟩
    | .and => ⟨4, by decide⟩
    | .or => ⟨5, by decide⟩
    | .invalid110 => ⟨6, by decide⟩
    | .invalid111 => ⟨7, by decide⟩
  decode := fun i =>
    match i.val with
    | 0 => .input | 1 => .constFalse | 2 => .constTrue | 3 => .neg
    | 4 => .and | 5 => .or | 6 => .invalid110 | _ => .invalid111
  decode_encode := by intro q; cases q <;> rfl

abbrev TagDecodeRep :=
  Sum Unit (Sum Bool (Sum (Bool × Bool) (Sum NeedExprTag Unit)))

def tagDecodeStateCodec : FinCodec TagDecodeState :=
  mapCodec
    (sumCodec unitCodec
      (sumCodec boolCodec
        (sumCodec (prodCodec boolCodec boolCodec)
          (sumCodec needExprTagCodec unitCodec))))
    (fun q =>
      match q with
      | .start => .inl ()
      | .bit1 b => .inr (.inl b)
      | .bit2 a b => .inr (.inr (.inl (a,b)))
      | .halt t => .inr (.inr (.inr (.inl t)))
      | .reject => .inr (.inr (.inr (.inr ()))))
    (fun r =>
      match r with
      | .inl _ => .start
      | .inr (.inl b) => .bit1 b
      | .inr (.inr (.inl (a,b))) => .bit2 a b
      | .inr (.inr (.inr (.inl t))) => .halt t
      | .inr (.inr (.inr (.inr _))) => .reject)
    (by intro q; cases q <;> rfl)

theorem tagDecodeStateCodec_size : tagDecodeStateCodec.size = 16 := by rfl

def framePushStateCodec : FinCodec FramePushState :=
  mapCodec
    (sumCodec evalFrameCodec
      (sumCodec evalFrameCodec
        (sumCodec evalFrameCodec (sumCodec unitCodec unitCodec))))
    (fun q =>
      match q with
      | .start f => .inl f
      | .after1 f => .inr (.inl f)
      | .after2 f => .inr (.inr (.inl f))
      | .halt => .inr (.inr (.inr (.inl ())))
      | .reject => .inr (.inr (.inr (.inr ()))))
    (fun r =>
      match r with
      | .inl f => .start f
      | .inr (.inl f) => .after1 f
      | .inr (.inr (.inl f)) => .after2 f
      | .inr (.inr (.inr (.inl _))) => .halt
      | .inr (.inr (.inr (.inr _))) => .reject)
    (by intro q; cases q <;> rfl)

theorem framePushStateCodec_size : framePushStateCodec.size = 23 := by rfl

def framePopStateCodec : FinCodec FramePopState :=
  mapCodec
    (sumCodec unitCodec
      (sumCodec unitCodec
        (sumCodec boolCodec
          (sumCodec boolCodec
            (sumCodec (prodCodec boolCodec boolCodec)
              (sumCodec (prodCodec boolCodec boolCodec)
                (sumCodec evalFrameCodec unitCodec)))))))
    (fun q =>
      match q with
      | .start => .inl ()
      | .read0 => .inr (.inl ())
      | .gap1 b => .inr (.inr (.inl b))
      | .read1 b => .inr (.inr (.inr (.inl b)))
      | .gap2 a b => .inr (.inr (.inr (.inr (.inl (a,b)))))
      | .read2 a b => .inr (.inr (.inr (.inr (.inr (.inl (a,b))))))
      | .halt f => .inr (.inr (.inr (.inr (.inr (.inr (.inl f))))))
      | .reject => .inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))
    (fun r =>
      match r with
      | .inl _ => .start
      | .inr (.inl _) => .read0
      | .inr (.inr (.inl b)) => .gap1 b
      | .inr (.inr (.inr (.inl b))) => .read1 b
      | .inr (.inr (.inr (.inr (.inl (a,b))))) => .gap2 a b
      | .inr (.inr (.inr (.inr (.inr (.inl (a,b)))))) => .read2 a b
      | .inr (.inr (.inr (.inr (.inr (.inr (.inl f)))))) => .halt f
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => .reject)
    (by intro q; cases q <;> rfl)

theorem framePopStateCodec_size : framePopStateCodec.size = 22 := by rfl

/-! Large evaluator composites. -/

abbrev NeedExprRep :=
  Sum CursorSeekState
    (Sum TagDecodeState
      (Sum InputNodeCompositeState
        (Sum (Bool × CursorReturnState)
          (Sum (EvalFrame × CursorReturnState)
            (Sum (EvalFrame × FramePushState)
              (Sum Bool (Sum Unit Unit)))))))

def needExprRepCodec : FinCodec NeedExprRep :=
  sumCodec cursorSeekCodec
    (sumCodec tagDecodeStateCodec
      (sumCodec inputNodeCompositeCodec
        (sumCodec (prodCodec boolCodec cursorReturnCodec)
          (sumCodec (prodCodec evalFrameCodec cursorReturnCodec)
            (sumCodec (prodCodec evalFrameCodec framePushStateCodec)
              (sumCodec boolCodec (sumCodec unitCodec unitCodec)))))))

def needExprCompositeCodec : FinCodec NeedExprCompositeState :=
  mapCodec needExprRepCodec
    (fun q =>
      match q with
      | .seek s => .inl s
      | .decode s => .inr (.inl s)
      | .input s => .inr (.inr (.inl s))
      | .retValue b s => .inr (.inr (.inr (.inl (b,s))))
      | .retPush f s => .inr (.inr (.inr (.inr (.inl (f,s)))))
      | .push f s => .inr (.inr (.inr (.inr (.inr (.inl (f,s))))))
      | .doneValue b => .inr (.inr (.inr (.inr (.inr (.inr (.inl b))))))
      | .doneNeed => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
      | .reject => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))))
    (fun r =>
      match r with
      | .inl s => .seek s
      | .inr (.inl s) => .decode s
      | .inr (.inr (.inl s)) => .input s
      | .inr (.inr (.inr (.inl (b,s)))) => .retValue b s
      | .inr (.inr (.inr (.inr (.inl (f,s))))) => .retPush f s
      | .inr (.inr (.inr (.inr (.inr (.inl (f,s)))))) => .push f s
      | .inr (.inr (.inr (.inr (.inr (.inr (.inl b)))))) => .doneValue b
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) => .doneNeed
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _))))))) => .reject)
    (by intro q; cases q <;> rfl)

theorem needExprCompositeCodec_size : needExprCompositeCodec.size = 401 := by rfl

abbrev HaveValueRep :=
  Sum Bool
    (Sum Bool
      (Sum (Bool × FramePopState)
        (Sum (EvalFrame × FramePushState)
          (Sum Bool (Sum Unit Unit)))))

def haveValueRepCodec : FinCodec HaveValueRep :=
  sumCodec boolCodec
    (sumCodec boolCodec
      (sumCodec (prodCodec boolCodec framePopStateCodec)
        (sumCodec (prodCodec evalFrameCodec framePushStateCodec)
          (sumCodec boolCodec (sumCodec unitCodec unitCodec)))))

def haveValueCompositeCodec : FinCodec HaveValueCompositeState :=
  mapCodec haveValueRepCodec
    (fun q =>
      match q with
      | .start b => .inl b
      | .peek b => .inr (.inl b)
      | .pop b s => .inr (.inr (.inl (b,s)))
      | .push f s => .inr (.inr (.inr (.inl (f,s))))
      | .doneValue b => .inr (.inr (.inr (.inr (.inl b))))
      | .doneNeed => .inr (.inr (.inr (.inr (.inr (.inl ())))))
      | .reject => .inr (.inr (.inr (.inr (.inr (.inr ()))))))
    (fun r =>
      match r with
      | .inl b => .start b
      | .inr (.inl b) => .peek b
      | .inr (.inr (.inl (b,s))) => .pop b s
      | .inr (.inr (.inr (.inl (f,s)))) => .push f s
      | .inr (.inr (.inr (.inr (.inl b)))) => .doneValue b
      | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .doneNeed
      | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .reject)
    (by intro q; cases q <;> rfl)

theorem haveValueCompositeCodec_size : haveValueCompositeCodec.size = 213 := by rfl

def syntaxModeCodec : FinCodec SyntaxMode where
  size := 3
  pos := by decide
  encode
    | .cnf => ⟨0, by decide⟩
    | .clause => ⟨1, by decide⟩
    | .mustInput => ⟨2, by decide⟩
  decode := fun i =>
    match i.val with | 0 => .cnf | 1 => .clause | _ => .mustInput
  decode_encode := by intro q; cases q <;> rfl

abbrev CheckedEvalRep :=
  Sum (SyntaxMode × NeedExprCompositeState)
    (Sum (SyntaxMode × HaveValueCompositeState)
      (Sum Bool (Sum Bool Unit)))

def checkedEvalRepCodec : FinCodec CheckedEvalRep :=
  sumCodec (prodCodec syntaxModeCodec needExprCompositeCodec)
    (sumCodec (prodCodec syntaxModeCodec haveValueCompositeCodec)
      (sumCodec boolCodec (sumCodec boolCodec unitCodec)))

def checkedEvalRunStateCodec : FinCodec CheckedEvalRunState :=
  mapCodec checkedEvalRepCodec
    (fun q =>
      match q with
      | .need m s => .inl (m,s)
      | .have m s => .inr (.inl (m,s))
      | .checkSource b => .inr (.inr (.inl b))
      | .final b => .inr (.inr (.inr (.inl b)))
      | .reject => .inr (.inr (.inr (.inr ()))))
    (fun r =>
      match r with
      | .inl (m,s) => .need m s
      | .inr (.inl (m,s)) => .have m s
      | .inr (.inr (.inl b)) => .checkSource b
      | .inr (.inr (.inr (.inl b))) => .final b
      | .inr (.inr (.inr (.inr _))) => .reject)
    (by intro q; cases q <;> rfl)

theorem checkedEvalRunStateCodec_size :
    checkedEvalRunStateCodec.size = 1847 := by rfl

abbrev CheckedVerifierRep :=
  Sum Unit
    (Sum (Fin 2)
      (Sum Unit (Sum CheckedEvalRunState Unit)))

def checkedVerifierRepCodec : FinCodec CheckedVerifierRep :=
  sumCodec unitCodec
    (sumCodec (finCodec 2 (by decide))
      (sumCodec unitCodec
        (sumCodec checkedEvalRunStateCodec unitCodec)))

def checkedVerifierStateCodec : FinCodec CheckedVerifierState :=
  mapCodec checkedVerifierRepCodec
    (fun q =>
      match q with
      | .start => .inl ()
      | .scan s => .inr (.inl s)
      | .enter => .inr (.inr (.inl ()))
      | .eval s => .inr (.inr (.inr (.inl s)))
      | .reject => .inr (.inr (.inr (.inr ()))))
    (fun r =>
      match r with
      | .inl _ => .start
      | .inr (.inl s) => .scan s
      | .inr (.inr (.inl _)) => .enter
      | .inr (.inr (.inr (.inl s))) => .eval s
      | .inr (.inr (.inr (.inr _))) => .reject)
    (by intro q; cases q <;> rfl)

theorem checkedVerifierStateCodec_size :
    checkedVerifierStateCodec.size = 1852 := by rfl

theorem checkedVerifier_decode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateCodec.decode (checkedVerifierStateCodec.encode q) = q :=
  checkedVerifierStateCodec.decode_encode q

#print axioms MCore.Real.P01CheckedVerifierStateCodec.checkedVerifier_decode_encode

end P01CheckedVerifierStateCodec
end Real
end MCore
