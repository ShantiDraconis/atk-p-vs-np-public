import MCore.Real.P01ParserWitnessComposition
import MCore.Real.CanonicalSATParserNTM

namespace MCore
namespace Real
namespace P01ParserFirewall

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATParserMachine
open CanonicalSATParserNTM
open P01ParserWitnessComposition

/-- The restored frozen parser is a total polynomial-time firewall for the
canonical circuit encoding. -/
theorem parser_halts_all
    (bs : BitString) :
    parserNTM.HaltsWithin
      (parserTimeBound bs.length)
      (initialNTMConfig parserNTM bs) :=
  parserPhaseCertificate.halts bs

/-- Decoder failure is exactly physical non-acceptance of the frozen Fin-25
parser at its certified polynomial bound. -/
theorem decode_none_iff_parser_not_accepts
    (bs : BitString) :
    decodeCircuit bs = none ↔
      ¬ parserNTM.AcceptsWithin
          (parserTimeBound bs.length)
          (initialNTMConfig parserNTM bs) := by
  rw [parserPhaseCertificate.accepts_iff_decode]
  constructor
  · intro hnone hex
    rcases hex with ⟨c, hc⟩
    rw [hnone] at hc
    contradiction
  · intro hnot
    cases hdec : decodeCircuit bs with
    | none =>
        rfl
    | some c =>
        exfalso
        exact hnot ⟨c, hdec⟩

/-- Dually, parser acceptance is exactly existence of the uniquely canonical
decoded circuit. -/
theorem parser_accepts_iff_decode_some
    (bs : BitString) :
    parserNTM.AcceptsWithin
        (parserTimeBound bs.length)
        (initialNTMConfig parserNTM bs) ↔
      ∃ c : CircuitK1.Circuit, decodeCircuit bs = some c :=
  parserPhaseCertificate.accepts_iff_decode bs

#print axioms MCore.Real.P01ParserFirewall.parser_halts_all
#print axioms MCore.Real.P01ParserFirewall.decode_none_iff_parser_not_accepts
#print axioms MCore.Real.P01ParserFirewall.parser_accepts_iff_decode_some

end P01ParserFirewall
end Real
end MCore
