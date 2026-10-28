import MCore.CircuitC2
import MCore.Real.P02BoundedComputationEncoding

namespace MCore.Real.Claim4NormalizedProgress

open MCore
open MCore.CircuitK1
open MCore.Real.P02BoundedComputationEncoding

def smartAnd : Circuit → Circuit → Circuit
  | .const true, y => y
  | x, .const true => x
  | .const false, _ => .const false
  | _, .const false => .const false
  | x, y => .and x y

def smartOr : Circuit → Circuit → Circuit
  | .const false, y => y
  | x, .const false => x
  | .const true, _ => .const true
  | _, .const true => .const true
  | x, y => .or x y

def clauseCircuitNorm : Clause → Circuit
  | [] => .const false
  | [l] => literalCircuit l
  | l :: ls => smartOr (literalCircuit l) (clauseCircuitNorm ls)

def cnfCircuitNorm : CNF → Circuit
  | [] => .const true
  | [clause] => clauseCircuitNorm clause
  | clause :: rest => smartAnd (clauseCircuitNorm clause) (cnfCircuitNorm rest)

def DNorm (ρ : Restriction) (t : Circuit) : Circuit :=
  MCore.CircuitC2.simplify
    (MCore.CircuitK1.restrict ρ (MCore.CircuitC2.simplify t))

def RestrictionProgressNorm (ρ : Restriction) (t : Circuit) : Prop :=
  DNorm ρ t ≠ MCore.CircuitC2.simplify t

theorem simplify_literalCircuit_idem (l : Literal) :
    MCore.CircuitC2.simplify (literalCircuit l) = literalCircuit l := by
  cases l with
  | mk v p =>
      cases p <;> rfl

theorem simplify_smartOr_of_fixed
    (x y : Circuit)
    (hx : MCore.CircuitC2.simplify x = x)
    (hy : MCore.CircuitC2.simplify y = y) :
    MCore.CircuitC2.simplify (smartOr x y) = smartOr x y := by
  cases x <;> cases y <;>
    simp_all [smartOr, MCore.CircuitC2.simplify] <;>
    split <;> simp_all [MCore.CircuitC2.simplify]

theorem simplify_smartAnd_of_fixed
    (x y : Circuit)
    (hx : MCore.CircuitC2.simplify x = x)
    (hy : MCore.CircuitC2.simplify y = y) :
    MCore.CircuitC2.simplify (smartAnd x y) = smartAnd x y := by
  cases x <;> cases y <;>
    simp_all [smartAnd, MCore.CircuitC2.simplify] <;>
    split <;> simp_all [MCore.CircuitC2.simplify]

theorem simplify_clauseCircuitNorm_idem (c : Clause) :
    MCore.CircuitC2.simplify (clauseCircuitNorm c) = clauseCircuitNorm c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      cases ls with
      | nil =>
          simpa [clauseCircuitNorm] using simplify_literalCircuit_idem l
      | cons l2 ls2 =>
          exact simplify_smartOr_of_fixed
            (literalCircuit l) (clauseCircuitNorm (l2 :: ls2))
            (simplify_literalCircuit_idem l) ih

theorem simplify_cnfCircuitNorm_idem (f : CNF) :
    MCore.CircuitC2.simplify (cnfCircuitNorm f) = cnfCircuitNorm f := by
  induction f with
  | nil => rfl
  | cons c cs ih =>
      cases cs with
      | nil =>
          simpa [cnfCircuitNorm] using simplify_clauseCircuitNorm_idem c
      | cons c2 cs2 =>
          exact simplify_smartAnd_of_fixed
            (clauseCircuitNorm c) (cnfCircuitNorm (c2 :: cs2))
            (simplify_clauseCircuitNorm_idem c) ih

theorem restrict_leavesZeroFree_id (c : Circuit) :
    MCore.CircuitK1.restrict MCore.CircuitK1.leavesZeroFree c = c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih => simp [MCore.CircuitK1.restrict, ih]
  | and a b iha ihb => simp [MCore.CircuitK1.restrict, iha, ihb]
  | or a b iha ihb => simp [MCore.CircuitK1.restrict, iha, ihb]

theorem leavesZeroFree_no_progress_norm (f : CNF) :
    ¬ RestrictionProgressNorm MCore.CircuitK1.leavesZeroFree (cnfCircuitNorm f) := by
  intro h
  apply h
  simp [DNorm, simplify_cnfCircuitNorm_idem, restrict_leavesZeroFree_id]

#print axioms MCore.Real.Claim4NormalizedProgress.leavesZeroFree_no_progress_norm

end MCore.Real.Claim4NormalizedProgress
