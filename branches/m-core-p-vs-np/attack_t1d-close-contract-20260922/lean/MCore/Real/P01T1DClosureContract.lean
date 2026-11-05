import MCore.Real.P01FullVerifierMachine
import MCore.Real.P01IntegratedNTMRequirements
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01T1DClosureContract

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01FullVerifierMachine
open P01IntegratedNTMRequirements
open P01FinalCertificate

structure T1DImplementationPackage where
  witnessPrep : WitnessPrepExecutionCertificate
  fullVerifier : FullVerifierCertificate
  integrated : P01MachineConstruction

def T1DImplementationGap : Prop :=
  Nonempty T1DImplementationPackage

theorem t1d_package_closes_p01
    (P : T1DImplementationPackage) :
    SATInNPGap circuitBitEncoding := by
  exact construction_closes_p01 ⟨P.integrated⟩

def FullVerifierImplementationGap : Prop :=
  Nonempty FullVerifierCertificate

def WitnessPrepExecutionGap : Prop :=
  Nonempty WitnessPrepExecutionCertificate

def IntegratedMachineGap : Prop :=
  Nonempty P01MachineConstruction

theorem t1d_gap_decomposes
    (h : T1DImplementationGap) :
    WitnessPrepExecutionGap ∧
    FullVerifierImplementationGap ∧
    IntegratedMachineGap := by
  rcases h with ⟨P⟩
  exact ⟨⟨P.witnessPrep⟩, ⟨P.fullVerifier⟩, ⟨P.integrated⟩⟩

#print axioms MCore.Real.P01T1DClosureContract.t1d_package_closes_p01
#print axioms MCore.Real.P01T1DClosureContract.t1d_gap_decomposes

end P01T1DClosureContract
end Real
end MCore
