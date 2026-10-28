
import MCore.Real.PNPNTMTableauEncoding
import MCore.Real.PNPNTMTableauFrontier

namespace MCore
namespace Real
namespace PNPNTMTableauClosure

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauFrontier
open PNPNTMTableauEncoding

structure NTMTableauCorrectnessCertificate where
  sound :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      SATLanguage (boundedExecCircuit_NTM M x t) ->
        M.machine.AcceptsWithin t
          (initialNTMConfig M.machine x)
  complete :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      M.machine.AcceptsWithin t
          (initialNTMConfig M.machine x) ->
        SATLanguage (boundedExecCircuit_NTM M x t)

structure NTMTableauSizeCertificate where
  coefficient : PolyNTMCandidate -> Nat
  exponent : PolyNTMCandidate -> Nat
  encoded_length_le :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      (encodeCircuit (boundedExecCircuit_NTM M x t)).length <=
        coefficient M * (x.length + t + 1) ^ exponent M

def ntmTableauProducerOfCertificates
    (C : NTMTableauCorrectnessCertificate)
    (S : NTMTableauSizeCertificate) :
    NTMTableauProducer where
  circuit := boundedExecCircuit_NTM
  isCNF := boundedExecCircuit_NTM_isCNF
  correctness := by
    intro M x t
    constructor
    · exact C.sound M x t
    · exact C.complete M x t
  coefficient := S.coefficient
  exponent := S.exponent
  encoded_length_le := S.encoded_length_le

theorem ntmTableauProducer_inhabited_of_certificates
    (C : NTMTableauCorrectnessCertificate)
    (S : NTMTableauSizeCertificate) :
    Nonempty NTMTableauProducer :=
  ⟨ntmTableauProducerOfCertificates C S⟩


def concreteCorrectnessCertificate : NTMTableauCorrectnessCertificate where
  sound := by
    intro M x t hSat
    exact tableau_soundness_from_satLanguage M x t hSat
  complete := by
    intro M x t hAcc
    exact tableau_completeness_to_satLanguage M x t hAcc

def concreteSizeCertificate : NTMTableauSizeCertificate where
  coefficient := tableauEncodingCoeff
  exponent := fun _ => 4
  encoded_length_le := by
    intro M x t
    exact boundedExec_encoded_length_poly M x t

def concreteNTMTableauProducer : NTMTableauProducer :=
  ntmTableauProducerOfCertificates
    concreteCorrectnessCertificate
    concreteSizeCertificate

theorem ntmTableauProducer_inhabited :
    Nonempty NTMTableauProducer :=
  ⟨concreteNTMTableauProducer⟩

theorem ntmTableauSizeCertificate_inhabited :
    Nonempty NTMTableauSizeCertificate :=
  ⟨concreteSizeCertificate⟩

def NTM_TABLEAU_SOUNDNESS_OPEN_MATH : Prop :=
  forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
    SATLanguage (boundedExecCircuit_NTM M x t) ->
      M.machine.AcceptsWithin t
        (initialNTMConfig M.machine x)

def NTM_TABLEAU_COMPLETENESS_OPEN_MATH : Prop :=
  forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
    M.machine.AcceptsWithin t
        (initialNTMConfig M.machine x) ->
      SATLanguage (boundedExecCircuit_NTM M x t)

def NTM_TABLEAU_SIZE_OPEN_MATH : Prop :=
  Nonempty NTMTableauSizeCertificate

#print axioms MCore.Real.PNPNTMTableauClosure.ntmTableauProducerOfCertificates
#print axioms MCore.Real.PNPNTMTableauClosure.ntmTableauProducer_inhabited_of_certificates

end PNPNTMTableauClosure
end Real
end MCore
