import MCore.Real.SevenLaneGreenGate

namespace MCore.Real.SevenLaneClaimBoundary

inductive ClaimKind where
  | skeleton
  | sourceMiddleOnly
  | realFrontierBound
  | historicallySolvedExternal
  deriving Repr, DecidableEq, BEq

structure LaneClaim where
  lane : String
  closedBaseRecordCount : Nat
  closedBridgeRecordCount : Nat
  sourceMiddleRecordCount : Nat
  materialGaps : Nat
  materialAtoms : Nat
  claimKind : ClaimKind
  terminalEndpointClosed : Bool
  buildVerified : Bool
  green : Bool
  deriving Repr, DecidableEq

def p01 : LaneClaim :=
  { lane := "P01_Riemann"
    closedBaseRecordCount := 3
    closedBridgeRecordCount := 1
    sourceMiddleRecordCount := 1
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p02 : LaneClaim :=
  { lane := "P02_YangMills"
    closedBaseRecordCount := 4
    closedBridgeRecordCount := 1
    sourceMiddleRecordCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p03 : LaneClaim :=
  { lane := "P03_PvsNP"
    closedBaseRecordCount := 6
    closedBridgeRecordCount := 4
    sourceMiddleRecordCount := 2
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p04 : LaneClaim :=
  { lane := "P04_NavierStokes"
    closedBaseRecordCount := 4
    closedBridgeRecordCount := 2
    sourceMiddleRecordCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p05 : LaneClaim :=
  { lane := "P05_Hodge"
    closedBaseRecordCount := 4
    closedBridgeRecordCount := 2
    sourceMiddleRecordCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p06 : LaneClaim :=
  { lane := "P06_BSD"
    closedBaseRecordCount := 4
    closedBridgeRecordCount := 2
    sourceMiddleRecordCount := 0
    materialGaps := 1
    materialAtoms := 2
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p07 : LaneClaim :=
  { lane := "P07_Poincare"
    closedBaseRecordCount := 0
    closedBridgeRecordCount := 0
    sourceMiddleRecordCount := 0
    materialGaps := 0
    materialAtoms := 0
    claimKind := .historicallySolvedExternal
    terminalEndpointClosed := true
    buildVerified := false
    green := false }

/-- The six currently open Millennium lanes tracked by this repository. -/
def openLaneClaims : List LaneClaim := [p01, p02, p03, p04, p05, p06]

def realFrontierBoundCount : Nat :=
  openLaneClaims.foldl
    (fun n L => if L.claimKind == .realFrontierBound then n + 1 else n) 0

def locallyGreenOpenLaneCount : Nat :=
  openLaneClaims.foldl (fun n L => if L.green then n + 1 else n) 0

theorem six_open_lanes_have_real_frontier_bound :
    realFrontierBoundCount = 6 := by decide

theorem no_open_lane_claims_terminal_closure :
    openLaneClaims.all (fun L => !L.terminalEndpointClosed) = true := by
  decide

theorem no_open_lane_claims_local_green :
    locallyGreenOpenLaneCount = 0 := by
  decide

/--
A frontier claim is strictly weaker than a solution claim in the current
manifest: every open lane has terminalEndpointClosed=false.
-/
theorem frontier_claim_not_solution_claim :
    ∀ L ∈ openLaneClaims, L.terminalEndpointClosed = false := by
  decide

/--
P07 is recorded as historically solved externally; this does not manufacture a
local build-verified formal proof in the current repository.
-/
theorem poincare_external_not_local_build :
    p07.claimKind = .historicallySolvedExternal ∧
    p07.terminalEndpointClosed = true ∧
    p07.buildVerified = false := by
  decide

#print axioms MCore.Real.SevenLaneClaimBoundary.six_open_lanes_have_real_frontier_bound
#print axioms MCore.Real.SevenLaneClaimBoundary.no_open_lane_claims_terminal_closure
#print axioms MCore.Real.SevenLaneClaimBoundary.no_open_lane_claims_local_green
#print axioms MCore.Real.SevenLaneClaimBoundary.frontier_claim_not_solution_claim
#print axioms MCore.Real.SevenLaneClaimBoundary.poincare_external_not_local_build

end MCore.Real.SevenLaneClaimBoundary
