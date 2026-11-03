import Mathlib
import MCore.Real.OpenMathCore.SelfQuotation
import MCore.Real.OpenMathCore.BoundedUniversalSimulation
import MCore.Real.OpenMathCore.SATCircuitCompiler
import MCore.Real.OpenMathCore.SameInputClosure
import MCore.Real.OpenMathCore.T5FBridge

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02UniversalFailureAlgebra
open P02G21G22Attack

structure TerminalArchitecture where
  selfDescription : SelfDescription
  simulator : BoundedUniversalSimulator
  compiler : SATCircuitCompiler
  sameInput : SameInputClosure

def TerminalArchitecture.toTerminalLaw
    (A : TerminalArchitecture) :
    TotalCandidateSeparationLaw where
  witness := A.sameInput.witness
  separates := by
    intro M _
    exact sameInputClosure_gives_mismatch A.sameInput M

def TerminalArchitecture.toT5FCore
    (A : TerminalArchitecture) : T5FCore :=
  separationLaw_implies_T5FCore A.toTerminalLaw

theorem terminalArchitecture_implies_G21
    (A : TerminalArchitecture) :
    G21Pointwise := by
  exact T5FCore_implies_G21 A.toT5FCore

theorem terminalArchitecture_implies_P02
    (A : TerminalArchitecture) :
    P02TerminalFrontier.P02Target := by
  exact T5FCore_implies_P02 A.toT5FCore

/-- Fail-closed endpoint: all preceding layers may exist while this remains open. -/
def SameInputClosureGap : Prop :=
  Nonempty SameInputClosure

theorem sameInputGap_implies_T5FCore
    (h : SameInputClosureGap) :
    T5FCore := by
  rcases h with ⟨S⟩
  intro M _
  exact ⟨S.witness M, sameInputClosure_gives_mismatch S M⟩

#print axioms MCore.Real.OpenMathCore.sameInputGap_implies_T5FCore
#print axioms MCore.Real.OpenMathCore.terminalArchitecture_implies_G21
#print axioms MCore.Real.OpenMathCore.terminalArchitecture_implies_P02

end MCore.Real.OpenMathCore
