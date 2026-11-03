import MCore.P012.P012Core

namespace MCore
namespace P012

inductive StatusProdutor where
  | zero_of_two
  | one_of_two
  | two_of_two
  deriving DecidableEq, Repr, BEq

def statusProd (p01 g21 : Option Bool) : StatusProdutor :=
  match p01, g21 with
  | none, none => .zero_of_two
  | some _, none => .one_of_two
  | none, some _ => .one_of_two
  | some _, some _ => .two_of_two

theorem L09_zero_two_never_rigid :
    statusProd none none ≠ .two_of_two := by
  decide

theorem L10_one_two_never_rigid (b : Bool) :
    statusProd (some b) none ≠ .two_of_two := by
  cases b <;> decide

theorem L11_two_two_is_rigid (p g : Bool) :
    statusProd (some p) (some g) = .two_of_two := by
  cases p <;> cases g <;> rfl

theorem L13_P01_closes_half :
    statusProd (some true) none = .one_of_two := rfl

/-- Canonical projection from the two-producer bookkeeping layer into the
P012 metamodel.  This map records status only. -/
def producerStatusToP012 : StatusProdutor → EstadoP012
  | .zero_of_two => .open0
  | .one_of_two => .open0
  | .two_of_two => .closed1

theorem two_of_two_maps_closed :
    producerStatusToP012 .two_of_two = .closed1 := rfl

theorem zero_of_two_not_closed :
    producerStatusToP012 .zero_of_two ≠ .closed1 := by
  decide

theorem one_of_two_not_closed :
    producerStatusToP012 .one_of_two ≠ .closed1 := by
  decide

/-- No inverse is provided: a closed P012 label cannot manufacture either
real producer. -/
def statusFromEvidence (p01Ready g21Ready : Bool) : StatusProdutor :=
  if p01Ready then
    if g21Ready then .two_of_two else .one_of_two
  else if g21Ready then
    .one_of_two
  else
    .zero_of_two

theorem both_true_status_closed :
    producerStatusToP012 (statusFromEvidence true true) = .closed1 := rfl

end P012
end MCore
