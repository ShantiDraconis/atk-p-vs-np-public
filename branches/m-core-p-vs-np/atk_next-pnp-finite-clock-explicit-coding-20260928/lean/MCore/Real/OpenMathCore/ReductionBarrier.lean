import Mathlib
import MCore.Real.P02CandidateCodingFrontier
import MCore.Real.P02DiagonalCompilerFrontierV2
import MCore.Real.P02KleeneBridgeAudit

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02CandidateCodingFrontier
open P02DiagonalCompilerFrontierV2

structure ReductionInfrastructure where
  coding : CandidateCodingInterface

def candidateCodeSize (R : ReductionInfrastructure) (M : PolyDTMCandidate) : Nat :=
  R.coding.codeSize M

theorem candidate_encode_injective
    (R : ReductionInfrastructure) :
    Function.Injective R.coding.encode :=
  P02CandidateCodingFrontier.encode_injective R.coding

/-- A barrier audit is metadata plus a theorem that a proposed shortcut does
not itself discharge the terminal separation law. -/
structure BarrierAudit (Shortcut : Prop) where
  terminal : Prop
  shortcut_not_terminal : Shortcut → terminal → False

def KleeneShortcut : Prop :=
  Nonempty P02KleeneSelfReferenceBridge.KleeneToSATBridge

def DiagonalTerminal : Prop :=
  P02FinalAttack.D3SemanticSelfReference

theorem kleene_shortcut_is_not_stronger :
    KleeneShortcut ↔ DiagonalTerminal :=
  P02KleeneBridgeAudit.kleeneBridge_iff_D3

/-- Natural-proof / relativization / algebrization are represented as explicit
obligations, not asserted as already overcome. -/
structure BarrierEscapeObligations where
  relativizationEscape : Prop
  naturalProofEscape : Prop
  algebrizationEscape : Prop

def BarrierEscapeGap : Prop :=
  Nonempty BarrierEscapeObligations

end MCore.Real.OpenMathCore
