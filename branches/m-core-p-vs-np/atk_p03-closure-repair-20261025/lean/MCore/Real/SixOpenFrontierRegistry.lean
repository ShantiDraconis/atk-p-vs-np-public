import MCore.Real.P01_Riemann.Architecture
import MCore.Real.P02_YangMills.Architecture
import MCore.Real.P03.Architecture
import MCore.Real.P04_NavierStokes.Architecture
import MCore.Real.P05_Hodge.Architecture
import MCore.Real.P06_BSD.Architecture

namespace MCore.Real.SixOpenFrontierRegistry

structure FrontierRecord where
  lane : String
  openBridge : String
  openMath : String
  materialGaps : Nat
  green : Bool
  buildVerified : Bool
  deriving Repr, DecidableEq

def frontiers : List FrontierRecord :=
  [ ⟨"P01_Riemann",
      "FiniteSpanApproximatesChi concreteGeneratorFamily",
      "RiemannHypothesis",
      1, false, false⟩
  , ⟨"P02_YangMills",
      "B60ConcretePhysicalAdapter",
      "YangMillsMassGap",
      1, false, false⟩
  , ⟨"P03_PvsNP",
      "Nonempty CompleteRouteBInhabitant",
      "PneqNP / RangeFailureLaw orientation",
      1, false, false⟩
  , ⟨"P04_NavierStokes",
      "ActualNSToSignedGainCore",
      "NavierStokesRegularity",
      1, false, false⟩
  , ⟨"P05_Hodge",
      "ConcreteAlgebraicityPayload",
      "RationalHodgeConjecture",
      1, false, false⟩
  , ⟨"P06_BSD",
      "RealizableBSDProducer",
      "BSD rank + refined formula",
      1, false, false⟩ ]

def totalIndependentMaterialGaps : Nat :=
  frontiers.foldl (fun n F => n + F.materialGaps) 0

def greenOpenProblemCount : Nat :=
  frontiers.foldl (fun n F => if F.green then n + 1 else n) 0

theorem six_open_frontiers :
    frontiers.length = 6 := by decide

theorem one_material_gap_per_open_lane :
    totalIndependentMaterialGaps = 6 := by decide

theorem no_open_lane_green :
    greenOpenProblemCount = 0 := by decide

theorem all_builds_unverified :
    frontiers.all (fun F => !F.buildVerified) = true := by decide

#print axioms MCore.Real.SixOpenFrontierRegistry.six_open_frontiers
#print axioms MCore.Real.SixOpenFrontierRegistry.one_material_gap_per_open_lane
#print axioms MCore.Real.SixOpenFrontierRegistry.no_open_lane_green
#print axioms MCore.Real.SixOpenFrontierRegistry.all_builds_unverified

end MCore.Real.SixOpenFrontierRegistry
