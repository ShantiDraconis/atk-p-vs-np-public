import MCore.P012.P012Core

namespace MCore
namespace P012

structure ThirdState where
  numerator : Int
  deriving DecidableEq, Repr

def thirdValueNumerator (s : ThirdState) : Int := s.numerator

def negTwoThirds : ThirdState := ⟨-2⟩
def negOneThird : ThirdState := ⟨-1⟩
def zeroThird : ThirdState := ⟨0⟩
def oneThird : ThirdState := ⟨1⟩
def twoThirds : ThirdState := ⟨2⟩
def threeThirds : ThirdState := ⟨3⟩
def negThreeThirds : ThirdState := ⟨-3⟩

def displacementNumerator (a b : ThirdState) : Int :=
  b.numerator - a.numerator

theorem negTwo_to_three_displacement :
    displacementNumerator negTwoThirds threeThirds = 5 := by
  decide

theorem two_to_three_displacement :
    displacementNumerator twoThirds threeThirds = 1 := by
  decide

theorem two_to_negThree_displacement :
    displacementNumerator twoThirds negThreeThirds = -5 := by
  decide

def UnitThirdStep (a b : ThirdState) : Prop :=
  b.numerator = a.numerator + 1

instance instDecidableUnitThirdStep (a b : ThirdState) :
    Decidable (UnitThirdStep a b) := by
  unfold UnitThirdStep
  infer_instance

theorem step_neg2_neg1 : UnitThirdStep negTwoThirds negOneThird := by decide
theorem step_neg1_zero : UnitThirdStep negOneThird zeroThird := by decide
theorem step_zero_one : UnitThirdStep zeroThird oneThird := by decide
theorem step_one_two : UnitThirdStep oneThird twoThirds := by decide
theorem step_two_three : UnitThirdStep twoThirds threeThirds := by decide

def fullCrossingPath : List ThirdState :=
  [negTwoThirds, negOneThird, zeroThird, oneThird, twoThirds, threeThirds]

theorem fullCrossingPath_length :
    fullCrossingPath.length = 6 := by
  decide

inductive Orientation where
  | negative
  | neutral
  | positive
  deriving DecidableEq, Repr, BEq

def orientation (s : ThirdState) : Orientation :=
  if s.numerator < 0 then .negative
  else if s.numerator = 0 then .neutral
  else .positive

theorem orientation_negTwo :
    orientation negTwoThirds = .negative := by decide

theorem orientation_zero :
    orientation zeroThird = .neutral := by decide

theorem orientation_three :
    orientation threeThirds = .positive := by decide

theorem orientation_two :
    orientation twoThirds = .positive := by decide

theorem orientation_negThree :
    orientation negThreeThirds = .negative := by decide

theorem negTwo_to_three_changes_orientation :
    orientation negTwoThirds ≠ orientation threeThirds := by decide

theorem two_to_negThree_changes_orientation :
    orientation twoThirds ≠ orientation negThreeThirds := by decide

#print axioms MCore.P012.negTwo_to_three_displacement
#print axioms MCore.P012.negTwo_to_three_changes_orientation

end P012
end MCore
