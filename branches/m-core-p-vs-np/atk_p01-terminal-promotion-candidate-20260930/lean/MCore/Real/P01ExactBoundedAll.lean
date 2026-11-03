import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedBinary

namespace MCore
namespace Real
namespace P01ExactBoundedAll

open CanonicalFinalProof
open CircuitK1
open CanonicalSATWitness
open P01CNFMode
open P01ExactBoundedCircuitProducer
open P01ExactBoundedBinary

/-- Canonical theorem assembling all five recursive circuit constructors into
one exact bounded physical certificate. No new hypothesis is introduced. -/
theorem exact_bounded_all
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : Circuit) (mode : SyntaxMode),
      ExactBoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_exact_bounded_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_exact_bounded_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_exact_bounded_certificate
        sigma witness mode child (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_exact_bounded_certificate sigma witness mode left right
        (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact or_exact_bounded_certificate sigma witness mode left right
        (ihLeft .clause) (ihRight .clause)

#print axioms MCore.Real.P01ExactBoundedAll.exact_bounded_all

end P01ExactBoundedAll
end Real
end MCore
