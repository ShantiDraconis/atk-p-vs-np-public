import Lean
import MCore.Integration.PNPCircularityAudit20261008

/-!
# Center transport audit — 2026-10-08

Question tested: does the START–CENTER–FINISH / structural-indeterminacy layer
of `ShantiDraconis/M-Core` already contain a proof that can be transported to
`G21Pointwise`, or a demonstrable logical incompatibility in the center?

Provenance of the ported declarations (copied verbatim, renamed into the
local `Port` namespace; ATK rule: no cross-repository proof dependency):
`ShantiDraconis/M-Core@53d58bceed3424a435eb54e01cd6d3f17324a630`
* `lean/MCore/FinalFail/ClosedCenterHard.lean`: `ClosedCenterHard`,
  `ClosedCenterTerminalChain`, `closed_center_terminal_chain_closure`
* `lean/MCore/FinalFail/MinimalOpenBridge.lean`: `Firewall`, `FirewallClosed`
* `lean/MCore/FinalFail/FundamentalIndeterminacy.lean`: `ResolvedCenter`,
  `CenterDetermined`, `FundamentalIndeterminacy`

Results, all kernel-checked below:
1. The ported layer never reaches the machine model (dependency walk), so
   none of its theorems can mention `PolyDTMCandidate`, SAT or `InP`.
2. `ClosedCenterHard` is inhabited for `G21Pointwise` and for its negation
   alike: the structure cannot distinguish the two answers.
3. A terminal chain ending in any `F` exists **iff** `F` is provable: the
   chain adds nothing; its arrows must already contain the proof. The
   proposed instance `ClosedCenterHard (P = NP) Center (P ≠ NP)` is
   refuted for every `Center` (it forces `¬ PneqNP ↔ PneqNP`).
4. `FirewallClosed` is satisfied by a firewall whose fields are all `True`:
   it does not inspect any code.
5. The actual P-vs-NP center is *determined* (excluded middle): it is not
   fundamentally indeterminate, yet determination does not reveal the branch.
6. Quantifier order: `∃ x, ∀ M, M fails at x` is provably FALSE for SAT
   (a one-state lookup machine is correct at any fixed input). Only
   `∀ M, ∃ x, …` (G21) is a meaningful target.

Conclusion: no transport from this layer to `G21Pointwise` exists or can
exist; the exact missing proposition remains `G21Pointwise` itself.
-/

namespace MCore.Integration.PNPCenterTransportAudit20261008

open MCore.Real
open CanonicalFinalProof
open MCore.Integration.PNPRecoveredFrontier20261008

namespace Port

structure ClosedCenterHard (Start Center Finish : Prop) where
  start_to_center : Start → Center
  center_to_start : Center → Start
  center_to_finish : Center → Finish
  finish_to_center : Finish → Center

structure Firewall where
  noSorry : Prop
  noAdmit : Prop
  noOracle : Prop
  noCircularity : Prop
  semanticFidelity : Prop

def FirewallClosed (f : Firewall) : Prop :=
  f.noSorry ∧ f.noAdmit ∧ f.noOracle ∧ f.noCircularity ∧ f.semanticFidelity

structure ClosedCenterTerminalChain (Start Center Finish : Prop) where
  startClosed : Start
  hard : ClosedCenterHard Start Center Finish
  firewall : Firewall
  firewallClosed : FirewallClosed firewall

theorem closed_center_terminal_chain_closure
    {Start Center Finish : Prop}
    (H : ClosedCenterTerminalChain Start Center Finish) : Finish :=
  H.hard.center_to_finish (H.hard.start_to_center H.startClosed)

structure ResolvedCenter where
  Branch : Type
  identity : Branch
  admissible : Branch → Prop
  identity_admissible : admissible identity

def CenterDetermined (R : ResolvedCenter) : Prop :=
  ∀ a b : R.Branch, R.admissible a → R.admissible b → a = b

def FundamentalIndeterminacy (R : ResolvedCenter) : Prop :=
  ∃ a b : R.Branch, R.admissible a ∧ R.admissible b ∧ a ≠ b

end Port

open Port

/-! ## 2. The closed-center structure is neutral between the two answers -/

def closedCenterHard_for_g21 :
    ClosedCenterHard G21Pointwise G21Pointwise G21Pointwise :=
  ⟨id, id, id, id⟩

def closedCenterHard_for_not_g21 :
    ClosedCenterHard (¬ G21Pointwise) (¬ G21Pointwise) (¬ G21Pointwise) :=
  ⟨id, id, id, id⟩

/-! ## 3. A terminal chain for `F` exists exactly when `F` is already proved -/

theorem terminalChain_exists_iff (F : Prop) :
    (∃ Start Center : Prop, Nonempty (ClosedCenterTerminalChain Start Center F)) ↔ F := by
  constructor
  · rintro ⟨_, _, ⟨H⟩⟩
    exact closed_center_terminal_chain_closure H
  · intro hF
    exact ⟨True, F, ⟨{
      startClosed := trivial
      hard := ⟨fun _ => hF, fun _ => trivial, id, id⟩
      firewall := ⟨True, True, True, True, True⟩
      firewallClosed := ⟨trivial, trivial, trivial, trivial, trivial⟩ }⟩⟩

/-- Specialization: a P ≠ NP terminal chain is exactly as hard as P ≠ NP. -/
theorem pneqnp_terminalChain_iff :
    (∃ Start Center : Prop, Nonempty (ClosedCenterTerminalChain Start Center PneqNP)) ↔
      PneqNP :=
  terminalChain_exists_iff PneqNP

/-- The instance `ClosedCenterHard (P = NP) Center (P ≠ NP)` proposed as a
transport is self-contradictory for every center: the structure forces
`Start ↔ Finish`, i.e. `¬ PneqNP ↔ PneqNP`. -/
theorem closedCenter_eq_to_neq_impossible (Center : Prop) :
    ¬ Nonempty (ClosedCenterHard (¬ PneqNP) Center PneqNP) := by
  rintro ⟨H⟩
  have toNeq : ¬ PneqNP → PneqNP := fun h => H.center_to_finish (H.start_to_center h)
  have toEq : PneqNP → ¬ PneqNP := fun h => H.center_to_start (H.finish_to_center h)
  have hn : ¬ PneqNP := fun hp => toEq hp hp
  exact hn (toNeq hn)

/-! ## 4. The firewall inspects nothing -/

theorem firewall_closed_by_true_fields :
    FirewallClosed ⟨True, True, True, True, True⟩ :=
  ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## 5. The real center is determined, but determination does not choose -/

open Classical in
/-- The P-vs-NP center: branch `true` is admissible iff G21 holds, branch
`false` iff it fails. The identity branch is the (unknown) true one. -/
noncomputable def pnpCenter : ResolvedCenter where
  Branch := Bool
  identity := if G21Pointwise then true else false
  admissible := fun b => if b then G21Pointwise else ¬ G21Pointwise
  identity_admissible := by
    by_cases h : G21Pointwise <;> simp [h]

theorem pnpCenter_determined : CenterDetermined pnpCenter := by
  intro a b ha hb
  cases a <;> cases b <;> simp_all [pnpCenter]

theorem pnpCenter_not_indeterminate : ¬ FundamentalIndeterminacy pnpCenter := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact hab (pnpCenter_determined a b ha hb)

theorem pnpCenter_true_branch_iff : pnpCenter.admissible true ↔ G21Pointwise :=
  Iff.rfl

/-! ## 6. Quantifier order: `∃ x ∀ M` failure is false for SAT -/

open Classical in
/-- One-state machine that halts immediately and answers SAT correctly at the
single fixed input `x` (classical constant). -/
noncomputable def lookupCandidate (x : BitString) : PolyDTMCandidate where
  stateCount := 0
  machine :=
    { initial := 0
      blank := none
      transition := fun q s => (q, s, .stay)
      halting := fun _ => true }
  blank_none := rfl
  accepting := fun _ => if SATTarget x then true else false
  timeBound := fun _ => 0
  time_poly := ⟨0, 0, fun _ => Nat.le_refl _⟩

theorem lookupCandidate_correctAt (x : BitString) :
    (lookupCandidate x).CorrectAt SATTarget x := by
  refine ⟨?_, ?_⟩
  · rfl
  · by_cases h : SATTarget x <;> simp [lookupCandidate, TM.run, h]

/-- `∃ x, ∀ M, M fails at x` is refuted: no single input defeats every
polynomial-time candidate. -/
theorem exists_forall_failure_false :
    ¬ ∃ x : BitString, ∀ M : PolyDTMCandidate, ¬ M.CorrectAt SATTarget x := by
  rintro ⟨x, hx⟩
  exact hx (lookupCandidate x) (lookupCandidate_correctAt x)

/-! ## 1. The ported center layer never reaches the machine model -/

open Lean Elab Command
open MCore.Integration.PNPCircularityAudit20261008 in
/-- Fails the build if any ported center declaration reaches a constant of the
machine/complexity model. A positive control checks the detector on
`pnpCenter`, which mentions `G21Pointwise` and must be flagged. -/
elab "#center_layer_model_free" : command => do
  let env ← getEnv
  let machineModel : List Name :=
    [`MCore.Real.CanonicalFinalProof.PolyDTMCandidate,
     `MCore.Real.CanonicalFinalProof.InP,
     `MCore.Real.CanonicalFinalProof.PneqNP,
     `MCore.Real.CanonicalSATBoundary.SATBits,
     `MCore.Real.TM,
     `MCore.Integration.PNPRecoveredFrontier20261008.G21Pointwise]
  let reaches (root : Name) : List Name :=
    (bfsDepths env root).toList.map (·.1) |>.filter machineModel.contains
  let control := reaches `MCore.Integration.PNPCenterTransportAudit20261008.pnpCenter
  if control.isEmpty then
    throwError "CENTER_AUDIT CONTROL FAIL: detector missed G21Pointwise in pnpCenter"
  let ported : List Name :=
    [`MCore.Integration.PNPCenterTransportAudit20261008.Port.ClosedCenterHard,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.ClosedCenterTerminalChain,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.closed_center_terminal_chain_closure,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.Firewall,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.FirewallClosed,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.ResolvedCenter,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.CenterDetermined,
     `MCore.Integration.PNPCenterTransportAudit20261008.Port.FundamentalIndeterminacy]
  for n in ported do
    let hit := reaches n
    unless hit.isEmpty do
      throwError "CENTER_AUDIT FAIL: {n} reaches machine model {hit}"
  logInfo m!"CENTER_AUDIT PASS: {ported.length} ported center declarations reach no machine-model constant; control flags {control}"

#center_layer_model_free

#print axioms terminalChain_exists_iff
#print axioms pneqnp_terminalChain_iff
#print axioms closedCenter_eq_to_neq_impossible
#print axioms firewall_closed_by_true_fields
#print axioms pnpCenter_determined
#print axioms pnpCenter_not_indeterminate
#print axioms lookupCandidate_correctAt
#print axioms exists_forall_failure_false

end MCore.Integration.PNPCenterTransportAudit20261008
