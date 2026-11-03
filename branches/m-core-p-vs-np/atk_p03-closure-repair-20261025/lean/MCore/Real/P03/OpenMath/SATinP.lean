import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
namespace MCore.Real.P03.OpenMath.SATinP
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
abbrev OpenTarget : Prop := InP (SATBits circuitBitEncoding)
end MCore.Real.P03.OpenMath.SATinP
