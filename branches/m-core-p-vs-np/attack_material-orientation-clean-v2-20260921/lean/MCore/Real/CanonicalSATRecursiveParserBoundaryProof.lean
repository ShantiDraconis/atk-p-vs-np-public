import MCore.Real.CanonicalSATRecursiveParserInitProof
import MCore.Real.CanonicalSATRecursiveParserPaths

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserBoundaryProof

open CanonicalFinalProof
open CanonicalSATSlotLog
open CanonicalSATRecursiveParserInitProof
open CanonicalSATRecursiveParserPaths

/-- The initializer boundary and the path-proof source configuration are the
same physical single-tape layout.  The work suffix is exactly the slot log;
sourceConfig inserts the unique blank delimiter. -/
theorem boundaryConfig_eq_sourceConfig
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    boundaryConfig leftBlankCount unread log =
      sourceConfig 4
        (List.replicate leftBlankCount none)
        unread
        (log.map some) := by
  cases unread <;>
    simp [boundaryConfig, sourceConfig]

/-- In particular, initialization reaches the exact one-slot source boundary
used by every subsequent parser-path theorem. -/
theorem parser_initializes_to_sourceConfig
    (bits : BitString) :
    CanonicalSATParserMachine.parserMachine.run (2 * bits.length + 4)
      (initialTMConfig CanonicalSATParserMachine.parserMachine bits) =
      sourceConfig 4 [none] bits (initialSlotLog.map some) := by
  rw [CanonicalSATRecursiveParserInitProof.parser_initializes]
  exact boundaryConfig_eq_sourceConfig 1 bits initialSlotLog

#print axioms MCore.Real.CanonicalSATRecursiveParserBoundaryProof.boundaryConfig_eq_sourceConfig
#print axioms MCore.Real.CanonicalSATRecursiveParserBoundaryProof.parser_initializes_to_sourceConfig

end CanonicalSATRecursiveParserBoundaryProof
end Real
end MCore
