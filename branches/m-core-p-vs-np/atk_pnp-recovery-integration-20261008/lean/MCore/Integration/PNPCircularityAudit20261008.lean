import Lean
import MCore.Integration.PNPRecoveredFrontier20261008

/-!
# Separation-of-concerns audit for the recovered P01 producer — 2026-10-08

Soundness of the P01 producer already follows from the kernel accepting it
with no hypotheses and only the standard axioms. This audit checks something
narrower: the SAT ∈ NP producer does not even *mention* any lower-bound or
separation object, so no part of the P01 side can be routing through the
conclusion.

The walk is breadth-first over the full transitive constant closure (types,
values, theorem bodies, opaque bodies, inductive constructors, and the
inductive of each constructor/recursor). Forbidden constants are matched by
full name (`forbiddenFull`) or by last component (`forbiddenLast`).

The positive control requires the detector to find a forbidden constant at
BFS depth ≥ 3 and exercises the failure branch, so a shallow or broken walk
cannot pass.
-/

open Lean Elab Command

namespace MCore.Integration.PNPCircularityAudit20261008

/-- Successors of one constant in the dependency graph. -/
def succs (env : Environment) (n : Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  match env.find? n with
  | some ci =>
    for c in ci.type.getUsedConstants do out := out.push c
    match ci with
    | .defnInfo v => for c in v.value.getUsedConstants do out := out.push c
    | .thmInfo v => for c in v.value.getUsedConstants do out := out.push c
    | .opaqueInfo v => for c in v.value.getUsedConstants do out := out.push c
    | .inductInfo v =>
      for c in v.ctors do out := out.push c
      for c in v.all do out := out.push c
    | .ctorInfo v => out := out.push v.induct
    | .recInfo v =>
      for c in v.all do out := out.push c
      for r in v.rules do
        for c in r.rhs.getUsedConstants do out := out.push c
    | _ => pure ()
  | none => pure ()
  return out

/-- BFS from `root`; returns every reached constant with its depth. -/
def bfsDepths (env : Environment) (root : Name) : Std.HashMap Name Nat := Id.run do
  let mut depth : Std.HashMap Name Nat := {}
  depth := depth.insert root 0
  let mut frontier : Array Name := #[root]
  let mut d := 0
  while !frontier.isEmpty do
    d := d + 1
    let mut next : Array Name := #[]
    for n in frontier do
      for c in succs env n do
        if !depth.contains c then
          depth := depth.insert c d
          next := next.push c
    frontier := next
  return depth

def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- Lower-bound / separation objects, matched by last name component. -/
def forbiddenLast : List String :=
  ["PneqNP", "OfficialPneqNP", "UniversalFailure", "FailureGenerator",
   "G21Pointwise", "G22Contradiction", "P02Target", "SATFailGap",
   "SATNotInP", "SeparationCertificate", "SATInternalClosure",
   "FinalGapCertificate", "InP", "PolyDTMRealization", "sorryAx"]

/-- Deterministic-candidate objects, matched by full name (their last
components, e.g. `CorrectAt`, also occur on the NTM side). -/
def forbiddenFull : List Name :=
  [`MCore.Real.CanonicalFinalProof.PolyDTMCandidate,
   `MCore.Real.CanonicalFinalProof.PolyDTMCandidate.CorrectAt]

def isForbidden (n : Name) : Bool :=
  forbiddenLast.contains (lastComponent n) || forbiddenFull.contains n

/-- Forbidden constants reachable from `root`, with BFS depth. -/
def forbiddenReached (env : Environment) (root : Name) : List (Name × Nat) :=
  (bfsDepths env root).toList.filter (fun p => isForbidden p.1)

def auditNoForbidden (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    throwError "audit target {root} not found"
  let size := (bfsDepths env root).size
  let bad := forbiddenReached env root
  if bad.isEmpty then
    logInfo m!"SEPARATION_AUDIT PASS {root}: {size} constants in closure, none forbidden"
  else
    throwError "SEPARATION_AUDIT FAIL {root}: reaches {bad}"

/-- Positive control. The conditional endpoint must reach forbidden
constants, including one at depth ≥ 3 (`PolyDTMRealization`, via
`PneqNP → InP → PolyDTMRealization`), and `auditNoForbidden` must take its
failure branch on it. -/
elab "#separation_audit_positive_control" : command => do
  let env ← getEnv
  let root := `MCore.Integration.PNPRecoveredFrontier20261008.pneqnp_of_g21
  let found := forbiddenReached env root
  let deep := found.filter (fun p => p.2 ≥ 3)
  if deep.isEmpty then
    throwError "SEPARATION_AUDIT CONTROL FAIL: no forbidden constant found at depth ≥ 3 ({found})"
  let failed ← try
      auditNoForbidden root
      pure false
    catch _ => pure true
  unless failed do
    throwError "SEPARATION_AUDIT CONTROL FAIL: failure branch not taken on {root}"
  logInfo m!"SEPARATION_AUDIT CONTROL PASS: {found.length} forbidden constants reached from {root}; depth ≥ 3: {deep}; failure branch exercised"

elab "#separation_audit_p01" : command =>
  auditNoForbidden `MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed

elab "#separation_audit_sat_in_np" : command =>
  auditNoForbidden `MCore.Integration.PNPRecoveredFrontier20261008.sat_in_np_recovered

#separation_audit_positive_control
#separation_audit_p01
#separation_audit_sat_in_np

end MCore.Integration.PNPCircularityAudit20261008
