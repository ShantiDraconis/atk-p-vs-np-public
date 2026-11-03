import MCore.Real.P01GlobalParserBound
import MCore.Real.CanonicalSATParserNTM
import MCore.Real.CanonicalSATWitnessGuessNTM
import MCore.Real.P01VerifiedRelation

namespace MCore
namespace Real
namespace P01ParserWitnessComposition

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATParserNTM
open CanonicalSATWitnessGuessNTM
open CanonicalSATWitness
open CanonicalSATVerifier
open P01GlobalParserBound
open P01VerifiedRelation

/-- T1.2 reuses the no-hypothesis T1.1 parser simulation as an NTM phase.
No endpoint assumption is introduced. -/
def parserPhaseCertificate : ParserNTMPhaseCertificate :=
  simulationToNTMPhase slot_parser_machine_simulation_certificate

/-- The witness generator is fixed finite control and has a polynomial bound. -/
theorem witness_guess_phase_polynomial :
    PolynomialTimeBound witnessGuessTimeBound :=
  witnessGuessTimeBound_poly

/-- The semantic handoff from parsed SAT to a finite short witness is already
exact at the canonical bit-language boundary. -/
theorem parsed_sat_iff_short_verified_witness
    (x : BitString) :
    CanonicalSATBoundary.SATBits circuitBitEncoding x ↔
      ∃ φ : CircuitK1.Circuit,
        decodeCircuit x = some φ ∧
        ∃ w : SATWitness φ,
          verifyWitness φ w = true ∧
          (witnessBits w).length ≤ (encodeCircuit φ).length :=
  satBits_iff_short_verified_witness x

#print axioms MCore.Real.P01ParserWitnessComposition.parserPhaseCertificate
#print axioms MCore.Real.P01ParserWitnessComposition.witness_guess_phase_polynomial
#print axioms MCore.Real.P01ParserWitnessComposition.parsed_sat_iff_short_verified_witness

end P01ParserWitnessComposition
end Real
end MCore
