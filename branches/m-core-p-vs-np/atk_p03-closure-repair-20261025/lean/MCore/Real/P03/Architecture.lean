import MCore.Real.P03.ClosedBase.C2I
import MCore.Real.P03.ClosedBase.R2I
import MCore.Real.P03.ClosedBase.PhiC
import MCore.Real.P03.ClosedBase.SPlus
import MCore.Real.P03.ClosedBase.SMinus
import MCore.Real.P03.ClosedBase.Nabla2
import MCore.Real.P03.ClosedBridge.ComplementReduce
import MCore.Real.P03.ClosedBridge.Dichotomy
import MCore.Real.P03.ClosedBridge.OddAntiRec
import MCore.Real.P03.ClosedBridge.Transport
import MCore.Real.P03.OpenBridge.BoundedCandidate
import MCore.Real.P03.OpenBridge.SourceLen
import MCore.Real.P03.OpenBridge.BoundedUnique
import MCore.Real.P03.OpenBridge.UniformDecoder
import MCore.Real.P03.OpenBridge.MFlipDepth
import MCore.Real.P03.OpenBridge.CompleteRouteB
import MCore.Real.P03.OpenMath.RangeFailureLaw
import MCore.Real.P03.OpenMath.SATinP

namespace MCore.Real.P03.Architecture

inductive LayerState where
  | closed
  | sourceClosedBuildUnverified
  | openBridge
  | blockedByOpenBridge
  | openMath
  deriving Repr, DecidableEq, BEq

structure LayerRecord where
  name : String
  state : LayerState
  note : String
  deriving Repr, DecidableEq

def closedBase : List LayerRecord :=
  [ ⟨"C2I", .closed, "ComplementSymmetry involution"⟩
  , ⟨"R2I", .closed, "CriticalReflection involution; not a claim that Cook-Levin R_M is involutive"⟩
  , ⟨"PhiC", .closed, "critical-half equivariance"⟩
  , ⟨"SPlus", .closed, "sum-of-squares zero characterization"⟩
  , ⟨"SMinus", .closed, "sum-of-squares zero characterization"⟩
  , ⟨"Nabla2", .closed, "rank-one outer-product Hessian entries"⟩ ]

def closedBridge : List LayerRecord :=
  [ ⟨"ComplementReduce", .closed, "CanonicalSAT(R_M x) iff not DeclaredAccepts M x"⟩
  , ⟨"Dichotomy", .closed, "ExistsPerfectFlip iff not RangeFailureLaw; classical dichotomy"⟩
  , ⟨"OddAntiRec", .closed, "PerfectFlip blocks odd observational recurrence"⟩
  , ⟨"Transport", .closed, "FullRun/RangeFailure conditional transport to internal PneqNP endpoint"⟩ ]

def openBridge : List LayerRecord :=
  [ ⟨"BoundedCandidate", .closed, "genuine source inhabits the bounded candidate space"⟩
  , ⟨"SourceLen", .sourceClosedBuildUnverified, "source-length bound present in source; build not verified here"⟩
  , ⟨"BoundedUnique", .blockedByOpenBridge, "material component of CompleteRouteB; not counted separately from the complete package"⟩
  , ⟨"UniformDecoder", .blockedByOpenBridge, "pointwise recovery closed; uniform effective decoder is blocked by BoundedUnique and algorithmic/poly obligations"⟩
  , ⟨"MFlipDepth", .blockedByOpenBridge, "physical depth-parity PerfectFlip construction is downstream of the uniform decoder"⟩
  , ⟨"CompleteRouteB", .openBridge, "complete material package: uniqueness + effective/poly decoder + strict growth + depth parity"⟩ ]

def openMath : List LayerRecord :=
  [ ⟨"RangeFailureLaw", .openMath, "P03 terminal A-side"⟩
  , ⟨"SATinP", .openMath, "alternative-side deterministic CanonicalSAT realization"⟩ ]

def allLayers : List LayerRecord :=
  closedBase ++ closedBridge ++ openBridge ++ openMath

def openBridgeCount : Nat :=
  allLayers.foldl (fun n r => if r.state == .openBridge then n + 1 else n) 0

def openMathCount : Nat :=
  allLayers.foldl (fun n r => if r.state == .openMath then n + 1 else n) 0

def green : Bool := false
def buildVerified : Bool := false

theorem closed_base_count : closedBase.length = 6 := by decide
theorem closed_bridge_count : closedBridge.length = 4 := by decide
theorem unique_open_bridge_count : openBridgeCount = 1 := by decide
theorem open_math_count : openMathCount = 2 := by decide
theorem architecture_green_false : green = false := rfl
theorem architecture_build_unverified : buildVerified = false := rfl

#print axioms MCore.Real.P03.Architecture.closed_base_count
#print axioms MCore.Real.P03.Architecture.closed_bridge_count
#print axioms MCore.Real.P03.Architecture.unique_open_bridge_count
#print axioms MCore.Real.P03.Architecture.open_math_count
#print axioms MCore.Real.P03.Architecture.architecture_green_false
#print axioms MCore.Real.P03.Architecture.architecture_build_unverified

end MCore.Real.P03.Architecture
