import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01PrefixFrameSemantics

open CircuitK1
open CanonicalSATFrameAttack

/-- Kernel-level semantics of direct prefix evaluation.  The physical machine
will realize the same descent/return discipline with frame data on tape. -/
inductive PrefixEval (sigma : Assignment) : Circuit -> Bool -> Prop where
  | input (i : Nat) :
      PrefixEval sigma (.input i) (sigma i)
  | const (b : Bool) :
      PrefixEval sigma (.const b) b
  | neg {c : Circuit} {v : Bool}
      (hc : PrefixEval sigma c v) :
      PrefixEval sigma (.not c) (!v)
  | and {a b : Circuit} {va vb : Bool}
      (ha : PrefixEval sigma a va)
      (hb : PrefixEval sigma b vb) :
      PrefixEval sigma (.and a b) (Bool.and va vb)
  | or {a b : Circuit} {va vb : Bool}
      (ha : PrefixEval sigma a va)
      (hb : PrefixEval sigma b vb) :
      PrefixEval sigma (.or a b) (Bool.or va vb)

/-- Every circuit has a direct prefix evaluation to its existing semantics. -/
theorem prefixEval_complete
    (sigma : Assignment) (c : Circuit) :
    PrefixEval sigma c (evalCircuit sigma c) := by
  induction c with
  | input i =>
      exact PrefixEval.input i
  | const b =>
      exact PrefixEval.const b
  | not c ih =>
      exact PrefixEval.neg ih
  | and a b iha ihb =>
      exact PrefixEval.and iha ihb
  | or a b iha ihb =>
      exact PrefixEval.or iha ihb

/-- Direct prefix evaluation is deterministic and agrees exactly with the
existing circuit semantics. -/
theorem prefixEval_sound
    {sigma : Assignment} {c : Circuit} {v : Bool}
    (h : PrefixEval sigma c v) :
    v = evalCircuit sigma c := by
  induction h with
  | input i =>
      rfl
  | const b =>
      rfl
  | neg hc ih =>
      simp [evalCircuit, ih]
  | and ha hb iha ihb =>
      simp [evalCircuit, iha, ihb]
  | or ha hb iha ihb =>
      simp [evalCircuit, iha, ihb]

theorem prefixEval_iff
    (sigma : Assignment) (c : Circuit) (v : Bool) :
    PrefixEval sigma c v <-> v = evalCircuit sigma c := by
  constructor
  · exact prefixEval_sound
  · intro hv
    subst v
    exact prefixEval_complete sigma c

/-- This is the exact semantic target for the physical frame evaluator. -/
def PhysicalPrefixFrameSemanticTarget
    (sigma : Assignment) (c : Circuit) (v : Bool) : Prop :=
  PrefixEval sigma c v

theorem physical_prefix_target_exact
    (sigma : Assignment) (c : Circuit) (v : Bool) :
    PhysicalPrefixFrameSemanticTarget sigma c v <->
      v = evalCircuit sigma c := by
  exact prefixEval_iff sigma c v

#print axioms MCore.Real.P01PrefixFrameSemantics.prefixEval_complete
#print axioms MCore.Real.P01PrefixFrameSemantics.prefixEval_sound
#print axioms MCore.Real.P01PrefixFrameSemantics.prefixEval_iff
#print axioms MCore.Real.P01PrefixFrameSemantics.physical_prefix_target_exact

end P01PrefixFrameSemantics
end Real
end MCore
