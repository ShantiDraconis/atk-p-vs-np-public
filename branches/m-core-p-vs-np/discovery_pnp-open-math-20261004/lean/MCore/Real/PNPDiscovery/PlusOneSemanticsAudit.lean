import MCore.Real.PNPDiscovery.ReadCone
import MCore.Real.PNPDiscovery.EncodingDependencyMap
import MCore.Real.PNPDiscovery.TableauShapeLeakage
import MCore.Real.PNPDiscovery.CanonicalClockNormalization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- +1 #1: stateCount stores the largest zero-based state index parameter,
so the actual finite state type has cardinality stateCount+1 and is never
empty. -/
theorem stateType_cardinality
    (M : PolyDTMCandidate) :
    Fintype.card (Fin (M.stateCount + 1)) =
      M.stateCount + 1 := by
  simp

theorem stateType_nonempty
    (M : PolyDTMCandidate) :
    Nonempty (Fin (M.stateCount + 1)) := by
  exact ⟨0⟩

/-- +1 #2: unary encodeNat uses n true bits plus one false terminator. -/
theorem unaryNat_plusOne_is_terminator
    (n : Nat) :
    (encodeNat n).length = n + 1 :=
  encodeNat_length n

/-- +1 #3: the retained tableau radius contains the input cells reachable
within t moves plus the currently scanned/head cell. -/
theorem radius_plusOne_is_headCell
    (x : BitString)
    (t : Nat) :
    ntmRadius x t = x.length + t + 1 := by
  rfl

/-- In equal-radius comparisons the radius +1 is not mathematical slack:
it cancels identically, leaving the exact conservation law |x|+t=|y|+u. -/
theorem equalRadius_cancels_plusOne
    (x y : BitString)
    (t u : Nat)
    (h :
      ntmRadius x t = ntmRadius y u) :
    x.length + t = y.length + u := by
  unfold ntmRadius at h
  omega

/-- +1 #4: a fuel-t run can inspect the initial head plus at most t rightward
source positions; therefore equality of t+1 source bits yields a radius-t
window equality. -/
theorem readCone_plusOne_is_initialHead
    (fuel : Nat)
    (x y : BitString)
    (h :
      x.take (fuel + 1) =
        y.take (fuel + 1)) :
    TapeWindowEq fuel (inputTape x) (inputTape y) :=
  initialTape_window_of_prefix fuel x y h

/-- +1 #5: polynomial envelopes use n+1 so the base is positive even at
zero-length input; this is part of the chosen bound convention, not an extra
machine step. -/
theorem polynomialBase_positive
    (n k : Nat) :
    0 < (n + 1) ^ k := by
  positivity

/-- SharedReadConePrefix inherits exactly the same head-cell +1. -/
theorem sharedReadCone_plusOne_unfold
    (M : PolyDTMCandidate)
    (x y : BitString) :
    SharedReadConePrefix M x y =
      Nat.min
        (M.timeBound x.length)
        (M.timeBound y.length) + 1 := by
  rfl

#print axioms MCore.Real.PNPDiscovery.stateType_cardinality
#print axioms MCore.Real.PNPDiscovery.unaryNat_plusOne_is_terminator
#print axioms MCore.Real.PNPDiscovery.equalRadius_cancels_plusOne
#print axioms MCore.Real.PNPDiscovery.readCone_plusOne_is_initialHead
#print axioms MCore.Real.PNPDiscovery.polynomialBase_positive

end PNPDiscovery
end Real
end MCore
