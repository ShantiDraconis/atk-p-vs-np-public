import MCore.K2

namespace MCore
namespace AutoCompose

structure TheoremCertificate (P : Prop) : Prop where
  proof : P

def ofProof {P : Prop} (h : P) : TheoremCertificate P := ⟨h⟩

def ofNode {n : CertNode} (c : ProofCertificate n) :
    TheoremCertificate n.statement := ⟨c.proof⟩

def map {P Q : Prop}
    (c : TheoremCertificate P)
    (f : P → Q) : TheoremCertificate Q := ⟨f c.proof⟩

def map₂ {P Q R : Prop}
    (cp : TheoremCertificate P)
    (cq : TheoremCertificate Q)
    (f : P → Q → R) : TheoremCertificate R := ⟨f cp.proof cq.proof⟩

def and {P Q : Prop}
    (cp : TheoremCertificate P)
    (cq : TheoremCertificate Q) :
    TheoremCertificate (P ∧ Q) := ⟨cp.proof, cq.proof⟩

def iffForward {P Q : Prop}
    (c : TheoremCertificate P)
    (h : P ↔ Q) : TheoremCertificate Q := ⟨h.mp c.proof⟩

def iffBackward {P Q : Prop}
    (c : TheoremCertificate Q)
    (h : P ↔ Q) : TheoremCertificate P := ⟨h.mpr c.proof⟩

def existsIntro {α : Sort _} {p : α → Prop}
    (a : α) (c : TheoremCertificate (p a)) :
    TheoremCertificate (∃ x, p x) := ⟨a, c.proof⟩

theorem extract {P : Prop} (c : TheoremCertificate P) : P := c.proof

def toNodeCertificate (n : CertNode)
    (hs : n.status = .provedProperty)
    (c : TheoremCertificate n.statement) :
    ProofCertificate n := ⟨hs, c.proof⟩

end AutoCompose
end MCore
