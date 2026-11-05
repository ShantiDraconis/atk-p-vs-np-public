import MCore.Real.P02LiteralFixedPointCountermodel
import MCore.Real.P02BoundedOpenMathFalsification
import MCore.Real.P02CompilerHaltingCounterexample
import MCore.Real.P02SameInputCoreFalsification
import MCore.Real.P02ReducedProducerFalsification

namespace MCore
namespace Real
namespace P02UniversalDiagonalFirewall

open CanonicalFinalProof
open P02ClockedDiagonalCompiler
open P02LiteralFixedPointCountermodel
open P02BoundedOpenMath
open P02BoundedOpenMathFalsification
open P02EffectiveCompilerConstruction
open P02CompilerHaltingCounterexample
open P02SameInputOnlyFrontier
open P02SameInputCoreFalsification
open P02FinalProofProducer
open P02ReducedProducerFalsification

/-- Canonical classes of diagonal constructions that the current formal
development has ruled out.  This is a classification object, not an endpoint
assumption. -/
inductive RefutedDiagonalRoute where
  | literalSemanticFixedPoint
  | boundedSameInput
  | strictSemanticCompiler
  | cookLevinSameInputCore
  | reducedLiteralProducer
  deriving DecidableEq, Repr

/-- Kernel-checkable firewall collecting the independent no-go theorems for
all currently refuted diagonal routes. -/
structure UniversalDiagonalRouteFirewall where
  no_literal :
    ¬ ∀ M : PolyDTMCandidate,
        ∃ x : BitString, semanticDiagonalBits M x = x
  no_bounded_same_input :
    ¬ BoundedSameInputEquation
  no_strict_compiler :
    ¬ UniformCompilerValueComputable
  no_same_input_core :
    ¬ Nonempty SameInputCore
  no_reduced_producer :
    ¬ Nonempty ReducedProducer

/-- The universal firewall is inhabited entirely by previously proved
countermodels/falsifications.  No new endpoint premise is introduced. -/
def universalDiagonalRouteFirewall :
    UniversalDiagonalRouteFirewall where
  no_literal :=
    no_universal_literal_fixed_point
  no_bounded_same_input :=
    not_BoundedSameInputEquation
  no_strict_compiler :=
    uniformCompilerValueComputable_false
  no_same_input_core :=
    not_SameInputCore
  no_reduced_producer :=
    not_ReducedProducer

/-- Every route in the classification has an explicit contradiction theorem
available from the universal firewall. -/
theorem route_refuted :
    ∀ r : RefutedDiagonalRoute,
      match r with
      | .literalSemanticFixedPoint =>
          ¬ ∀ M : PolyDTMCandidate,
              ∃ x : BitString, semanticDiagonalBits M x = x
      | .boundedSameInput =>
          ¬ BoundedSameInputEquation
      | .strictSemanticCompiler =>
          ¬ UniformCompilerValueComputable
      | .cookLevinSameInputCore =>
          ¬ Nonempty SameInputCore
      | .reducedLiteralProducer =>
          ¬ Nonempty ReducedProducer := by
  intro r
  cases r with
  | literalSemanticFixedPoint =>
      exact universalDiagonalRouteFirewall.no_literal
  | boundedSameInput =>
      exact universalDiagonalRouteFirewall.no_bounded_same_input
  | strictSemanticCompiler =>
      exact universalDiagonalRouteFirewall.no_strict_compiler
  | cookLevinSameInputCore =>
      exact universalDiagonalRouteFirewall.no_same_input_core
  | reducedLiteralProducer =>
      exact universalDiagonalRouteFirewall.no_reduced_producer

/-- Universal no-go theorem: none of the five refuted construction classes can
serve as a terminal G21 inhabitant.  This deliberately does not assert that
all possible diagonal constructions are impossible. -/
theorem universal_refuted_route_conjunction :
    (¬ ∀ M : PolyDTMCandidate,
        ∃ x : BitString, semanticDiagonalBits M x = x) ∧
    (¬ BoundedSameInputEquation) ∧
    (¬ UniformCompilerValueComputable) ∧
    (¬ Nonempty SameInputCore) ∧
    (¬ Nonempty ReducedProducer) := by
  exact
    ⟨ universalDiagonalRouteFirewall.no_literal,
      universalDiagonalRouteFirewall.no_bounded_same_input,
      universalDiagonalRouteFirewall.no_strict_compiler,
      universalDiagonalRouteFirewall.no_same_input_core,
      universalDiagonalRouteFirewall.no_reduced_producer ⟩

#print axioms MCore.Real.P02UniversalDiagonalFirewall.universalDiagonalRouteFirewall
#print axioms MCore.Real.P02UniversalDiagonalFirewall.route_refuted
#print axioms MCore.Real.P02UniversalDiagonalFirewall.universal_refuted_route_conjunction

end P02UniversalDiagonalFirewall
end Real
end MCore
