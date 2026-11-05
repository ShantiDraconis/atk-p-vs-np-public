import Mathlib
import MCore.Real.OpenMathCore.NumericClasses

namespace MCore.Real.OpenMathCore

def Trajectory := ℝ → ℝ

structure TopologicalBehavior where
  trajectory : Trajectory
  continuous : Continuous trajectory

structure AsymptoticBehavior where
  trajectory : Trajectory
  limit : ℝ
  tends : Filter.Tendsto trajectory Filter.atTop (nhds limit)

def constantTopologicalBehavior (c : ℝ) : TopologicalBehavior where
  trajectory := fun _ => c
  continuous := continuous_const

def constantAsymptoticBehavior (c : ℝ) : AsymptoticBehavior where
  trajectory := fun _ => c
  limit := c
  tends := tendsto_const_nhds

structure NeighborhoodInvariant where
  carrier : Set ℝ
  isOpen_carrier : IsOpen carrier
  preserved : ∀ x ∈ carrier, ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ carrier

end MCore.Real.OpenMathCore
