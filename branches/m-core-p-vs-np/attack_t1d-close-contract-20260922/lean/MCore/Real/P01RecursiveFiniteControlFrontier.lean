import MCore.Real.CanonicalSATFrameMachineV2
import MCore.Real.P01VerifiedRelation
import MCore.Real.P01ComponentFailProof

namespace MCore
namespace Real
namespace P01RecursiveFiniteControlFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATParserAttack
open CanonicalSATFrameMachineV2
open CanonicalSATNTMAttack
open P01ComponentFailProof

/-!
P01 recursive finite-control frontier.

This file intentionally does not add a second parser model.

The canonical parser contract already enforces, by type:
* finite control: Fin (stateCount + 1);
* fixed tape alphabet: Option Bool;
* canonical input tape;
* blank = none;
* a polynomial time bound;
* halting on every bitstring;
* exact acceptance iff decodeCircuit succeeds.

Consequently a state carrying an arbitrary Circuit/CNF and a symbol carrying
String/List Bool cannot inhabit this contract. No boolean "audit flag" is used
for those properties: the Lean types themselves are the firewall.
-/

/-- The exact parser object still required by P01. -/
abbrev RecursiveFiniteControlParserCertificate :=
  CanonicalRecursiveParserMachineCertificate

/-- The exact parser existence gate. No witness is manufactured here. -/
abbrev RecursiveFiniteControlParserClosed : Prop :=
  CanonicalRecursiveParserOperationalGap

/-- The concrete frame command machine is a genuine finite-control/fixed-
alphabet implementation. This theorem records its type-level boundary without
claiming it is already the complete recursive parser. -/
theorem frame_machine_has_canonical_machine_type :
    ∃ stateCount : Nat,
      Nonempty (TM (Fin (stateCount + 1)) (Option Bool)) := by
  exact ⟨4, ⟨frameCommandMachine⟩⟩

/-- The recovered frame machine closes only its own hardened frame protocol.
It is deliberately weaker than the recursive-parser target. -/
theorem frame_protocol_source_closed :
    BlankNormalizedFrameTapeOperationalGap :=
  blank_normalized_frame_tape_operational_closed

/-- Any genuine recursive parser automatically supplies the legacy parser
payload, but not conversely. -/
theorem recursive_parser_implies_legacy_parser :
    RecursiveFiniteControlParserClosed →
      RecursiveParserOperationalGap :=
  canonical_recursive_parser_closes_legacy_gap

/-- P01 remains exactly the canonical SAT-in-NP realization target. A parser
certificate is necessary engineering input, but this file does not pretend
that parser existence alone constructs the full nondeterministic realization. -/
abbrev P01Target : Prop :=
  CanonicalSATMachineClosure

/-- Promotion firewall: the only accepted P01 endpoint is the existing
CanonicalSATMachineClosure. This is intentionally identity-like: it prevents
weaker parser/frame records from being renamed as P01. -/
theorem p01_promotion_requires_canonical_closure
    (h : P01Target) :
    CanonicalSATMachineClosure :=
  h

/-- Current exact conjunction used by the runner. It is a frontier, not a
claim that the conjunction is inhabited. -/
def P01OperationalFrontier : Prop :=
  RecursiveFiniteControlParserClosed ∧
  CanonicalSATMachineClosure

theorem p01_frontier_implies_target
    (h : P01OperationalFrontier) :
    CanonicalSATMachineClosure :=
  h.2

#print axioms MCore.Real.P01RecursiveFiniteControlFrontier.frame_machine_has_canonical_machine_type
#print axioms MCore.Real.P01RecursiveFiniteControlFrontier.frame_protocol_source_closed
#print axioms MCore.Real.P01RecursiveFiniteControlFrontier.recursive_parser_implies_legacy_parser
#print axioms MCore.Real.P01RecursiveFiniteControlFrontier.p01_promotion_requires_canonical_closure
#print axioms MCore.Real.P01RecursiveFiniteControlFrontier.p01_frontier_implies_target

end P01RecursiveFiniteControlFrontier
end Real
end MCore
