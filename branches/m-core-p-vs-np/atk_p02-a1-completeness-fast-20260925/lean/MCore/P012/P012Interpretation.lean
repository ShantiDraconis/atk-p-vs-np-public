import MCore.P012.P012MetaClosure
import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack

namespace MCore
namespace P012

open Real
open Real.P01FinalCertificate
open Real.P02G21G22Attack

inductive PipelineState where
  | open
  | closed
  | unresolved
  | invalid
  deriving DecidableEq, Repr, BEq

def interpretP012 : EstadoP012 → PipelineState
  | .open0 => .open
  | .closed1 => .closed
  | .indet => .unresolved
  | .inf => .invalid

theorem interpret_open0 :
    interpretP012 .open0 = .open := rfl

theorem interpret_closed1 :
    interpretP012 .closed1 = .closed := rfl

theorem interpret_indet :
    interpretP012 .indet = .unresolved := rfl

theorem interpret_inf :
    interpretP012 .inf = .invalid := rfl

/-- Status extracted from actual real producer evidence.
The proofs are inputs; no converse is defined. -/
def realProducerStatus
    (_hp01 : P01ConstructionGap)
    (_hg21 : G21Pointwise) :
    StatusProdutor :=
  .two_of_two

theorem real_two_producers_have_two_of_two
    (hp01 : P01ConstructionGap)
    (hg21 : G21Pointwise) :
    realProducerStatus hp01 hg21 = .two_of_two := rfl

/-- Safe bridge: actual P01 + actual G21 evidence may be observed as the
closed P012 status.  This theorem creates no mathematical producer. -/
theorem real_two_producers_imply_p012_closed
    (hp01 : P01ConstructionGap)
    (hg21 : G21Pointwise) :
    interpretP012
      (producerStatusToP012 (realProducerStatus hp01 hg21)) =
      .closed := by
  rfl

/-- The real downstream theorem remains the repository theorem, not a P012
definition. Once both real producers exist, invoke the already formalized
internal separation consumer. -/
theorem real_two_producers_close_internal
    (hp01 : P01ConstructionGap)
    (hg21 : G21Pointwise) :
    CanonicalFinalProof.PneqNP := by
  exact Real.P02G21G22Attack.p01_g21_closes_internal
    (Real.P01FinalCertificate.construction_closes_p01 hp01)
    hg21

/-
There is intentionally no theorem from EstadoP012.closed1 to
P01ConstructionGap and G21Pointwise. The metamodel is observational and
one-way.
-/

#print axioms MCore.P012.real_two_producers_imply_p012_closed
#print axioms MCore.P012.real_two_producers_close_internal

end P012
end MCore
