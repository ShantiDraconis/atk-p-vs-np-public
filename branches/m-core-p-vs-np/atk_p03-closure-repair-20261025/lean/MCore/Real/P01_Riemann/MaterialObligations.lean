import MCore.Real.P01_Riemann.OpenBridge.BoundedZeroCandidate

namespace MCore.Real.P01_Riemann.MaterialObligations

inductive ObligationState where
  | open
  | blocked
  | closed
  deriving Repr, DecidableEq, BEq

structure Obligation where
  name : String
  state : ObligationState
  scope : String
  deriving Repr, DecidableEq

def obligations : List Obligation :=
  [ ⟨"BoundedZeroFinite", .open,
      "prove finite zero set in each bounded critical-strip window"⟩
  , ⟨"BoundedZeroEffectiveEnumeration", .open,
      "construct a certified effective enumeration/root-isolation procedure for that finite window"⟩
  , ⟨"RHUniformPassage", .blocked,
      "upgrade all bounded-window certificates uniformly to the terminal RH endpoint"⟩ ]

def atomicOpenCount : Nat :=
  obligations.foldl (fun n o => if o.state == .open then n + 1 else n) 0

theorem atomic_open_count : atomicOpenCount = 2 := by decide
def green : Bool := false
theorem green_false : green = false := rfl

#print axioms MCore.Real.P01_Riemann.MaterialObligations.atomic_open_count
#print axioms MCore.Real.P01_Riemann.MaterialObligations.green_false

end MCore.Real.P01_Riemann.MaterialObligations
