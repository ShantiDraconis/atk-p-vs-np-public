import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalFinalProof

def PvsNPTerminalCertifies : Prop :=
  PneqNP

def PvsNPTerminalRefutes : Prop :=
  ¬ PneqNP

def PvsNPProducer : Prop :=
  Nonempty SeparationCertificate

theorem pvsnp_producer_certifies_terminal
    (h : PvsNPProducer) :
    PvsNPTerminalCertifies := by
  rcases h with ⟨cert⟩
  exact separation_certificate_closes cert

theorem not_pvsnpTerminalCertifies_iff_refutes :
    ¬ PvsNPTerminalCertifies ↔ PvsNPTerminalRefutes := by
  rfl

theorem pvsnp_terminal_cert_refute_disjoint :
    ¬ (PvsNPTerminalCertifies ∧ PvsNPTerminalRefutes) := by
  rintro ⟨hcert, href⟩
  exact href hcert

theorem universalFailure_plus_np_certifies_terminal
    {language : BitLanguage}
    (hNP : InNP language)
    (hFail : UniversalFailure language) :
    PvsNPTerminalCertifies :=
  target_failure_implies_p_ne_np hNP hFail

end CanonicalFinalProof
end Real
end MCore
