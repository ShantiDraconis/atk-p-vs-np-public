import MCore.Real.P01RawTotalizationProducer

/-!
# P vs NP depois do P01 (13/10/2026)

O P01 está fechado no modelo endurecido do programa:
`P01RawTotalizationProducer.p01ConstructionGap_closed : P01ConstructionGap`
(certificado de 09/10/2026, auditoria `P01 closure audit`, run 37913791428).

Este módulo apenas recompõe esse certificado com os teoremas de `CanonicalFinalProof`:

* `sat_in_np` — SAT ∈ NP no modelo, **incondicional**;
* `pneqnp_of_universal_failure` — P ≠ NP no modelo segue SÓ da falha universal para SAT (G2.1);
* `pneqnp_of_sat_not_in_p` — forma equivalente: só falta `SAT ∉ P`;
* `sat_in_p_iff_no_failure` — a lacuna restante é exatamente a negação de um decisor polinomial.

A lacuna G2.1 (`UniversalFailure (SATBits circuitBitEncoding)`) continua aberta: é o conteúdo de P ≠ NP.
-/

namespace MCore
namespace Real
namespace PNPAfterP01

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-- SAT ∈ NP no modelo endurecido — incondicional (P01 fechado). -/
theorem sat_in_np : InNP (SATBits circuitBitEncoding) :=
  P01FinalCertificate.construction_closes_p01
    P01RawTotalizationProducer.p01ConstructionGap_closed

/-- Com P01 fechado, a separação depende só de G2.1. -/
theorem pneqnp_of_universal_failure
    (h : UniversalFailure (SATBits circuitBitEncoding)) : PneqNP :=
  target_failure_implies_p_ne_np sat_in_np h

/-- Forma equivalente: só falta `SAT ∉ P`. -/
theorem pneqnp_of_sat_not_in_p
    (h : ¬ InP (SATBits circuitBitEncoding)) : PneqNP :=
  pneqnp_of_universal_failure (universal_failure_iff_not_in_p.mpr h)

/-- A lacuna restante é exatamente a ausência de decisor determinístico polinomial para SAT. -/
theorem sat_in_p_iff_no_failure :
    InP (SATBits circuitBitEncoding) ↔ ¬ UniversalFailure (SATBits circuitBitEncoding) := by
  rw [universal_failure_iff_not_in_p]
  constructor
  · intro h hn
    exact hn h
  · intro h
    exact Classical.byContradiction h

#print axioms MCore.Real.PNPAfterP01.sat_in_np
#print axioms MCore.Real.PNPAfterP01.pneqnp_of_universal_failure
#print axioms MCore.Real.PNPAfterP01.pneqnp_of_sat_not_in_p
#print axioms MCore.Real.PNPAfterP01.sat_in_p_iff_no_failure

end PNPAfterP01
end Real
end MCore
