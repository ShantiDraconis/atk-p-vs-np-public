import MCore.Real.P01PrefixFrameSemantics
import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01PrefixFrameValueSemantics

open CircuitK1
open CanonicalSATFrameAttack

/-- Semantic continuation using exactly the five fixed-width physical parser
frames already implemented by CanonicalSATFrameMachineV2.  The Boolean values
needed across binary children live on a separate value stack. -/
inductive FrameValueEval (sigma : Assignment) :
    Circuit -> List Frame -> List Bool -> Bool -> Prop where
  | input (i : Nat) (fs : List Frame) (vs : List Bool) :
      FrameValueEval sigma (.input i) fs vs (sigma i)
  | const (b : Bool) (fs : List Frame) (vs : List Bool) :
      FrameValueEval sigma (.const b) fs vs b
  | neg {c : Circuit} {fs : List Frame} {vs : List Bool} {v : Bool}
      (hc : FrameValueEval sigma c (.neg :: fs) vs v) :
      FrameValueEval sigma (.not c) fs vs (!v)
  | andNode {a b : Circuit} {fs : List Frame} {vs : List Bool}
      {va vb : Bool}
      (ha : FrameValueEval sigma a (.andLeft :: fs) vs va)
      (hb : FrameValueEval sigma b (.andRight :: fs) (va :: vs) vb) :
      FrameValueEval sigma (.and a b) fs vs (Bool.and va vb)
  | orNode {a b : Circuit} {fs : List Frame} {vs : List Bool}
      {va vb : Bool}
      (ha : FrameValueEval sigma a (.orLeft :: fs) vs va)
      (hb : FrameValueEval sigma b (.orRight :: fs) (va :: vs) vb) :
      FrameValueEval sigma (.or a b) fs vs (Bool.or va vb)

/-- Completeness against the repository's existing circuit semantics. -/
theorem frameValueEval_complete
    (sigma : Assignment) (c : Circuit)
    (fs : List Frame) (vs : List Bool) :
    FrameValueEval sigma c fs vs (evalCircuit sigma c) := by
  induction c generalizing fs vs with
  | input i =>
      exact FrameValueEval.input i fs vs
  | const b =>
      exact FrameValueEval.const b fs vs
  | not c ih =>
      exact FrameValueEval.neg (ih (.neg :: fs) vs)
  | and a b iha ihb =>
      exact FrameValueEval.andNode
        (iha (.andLeft :: fs) vs)
        (ihb (.andRight :: fs) (evalCircuit sigma a :: vs))
  | or a b iha ihb =>
      exact FrameValueEval.orNode
        (iha (.orLeft :: fs) vs)
        (ihb (.orRight :: fs) (evalCircuit sigma a :: vs))

/-- Soundness: the fixed-width frame/value discipline computes no alternative
Boolean; every successful evaluation is exactly evalCircuit. -/
theorem frameValueEval_sound
    {sigma : Assignment} {c : Circuit} {fs : List Frame}
    {vs : List Bool} {v : Bool}
    (h : FrameValueEval sigma c fs vs v) :
    v = evalCircuit sigma c := by
  induction h with
  | input i fs vs =>
      rfl
  | const b fs vs =>
      rfl
  | neg hc ih =>
      simp [evalCircuit, ih]
  | andNode ha hb iha ihb =>
      simp [evalCircuit, iha, ihb]
  | orNode ha hb iha ihb =>
      simp [evalCircuit, iha, ihb]

theorem frameValueEval_iff
    (sigma : Assignment) (c : Circuit)
    (fs : List Frame) (vs : List Bool) (v : Bool) :
    FrameValueEval sigma c fs vs v <-> v = evalCircuit sigma c := by
  constructor
  · exact frameValueEval_sound
  · intro hv
    subst v
    exact frameValueEval_complete sigma c fs vs

/-- This is the semantic contract for the integrated physical parser/evaluator:
the frame alphabet is now exactly the already-certified three-bit frame code. -/
def IntegratedPrefixPhysicalTarget
    (sigma : Assignment) (c : Circuit) (v : Bool) : Prop :=
  FrameValueEval sigma c [] [] v

theorem integratedPrefixPhysicalTarget_exact
    (sigma : Assignment) (c : Circuit) (v : Bool) :
    IntegratedPrefixPhysicalTarget sigma c v <->
      v = evalCircuit sigma c := by
  exact frameValueEval_iff sigma c [] [] v

#print axioms MCore.Real.P01PrefixFrameValueSemantics.frameValueEval_complete
#print axioms MCore.Real.P01PrefixFrameValueSemantics.frameValueEval_sound
#print axioms MCore.Real.P01PrefixFrameValueSemantics.integratedPrefixPhysicalTarget_exact

end P01PrefixFrameValueSemantics
end Real
end MCore
