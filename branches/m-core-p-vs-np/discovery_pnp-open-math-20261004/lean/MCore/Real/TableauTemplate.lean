import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace TableauTemplate

open CanonicalFinalProof
open PNPNTMTableauEncoding

/--
The structural parameters that determine the tableau layout for a fixed
machine/input-length/time triple. Input bits are supplied only at
instantiation time.
-/
structure TableauTemplate (M : PolyNTMCandidate) where
  n : Nat
  t : Nat

def tableauTemplate
    (M : PolyNTMCandidate)
    (n t : Nat) :
    TableauTemplate M :=
  ⟨n, t⟩

def templateInitial
    {M : PolyNTMCandidate}
    (T : TableauTemplate M)
    (x : BitString) : NTMCNF :=
  ntmInitialCNF M x T.t

def templateTransitions
    {M : PolyNTMCandidate}
    (T : TableauTemplate M)
    (x : BitString) : NTMCNF :=
  ntmTransitionsCNF M x T.t

def templateFinal
    {M : PolyNTMCandidate}
    (T : TableauTemplate M) : NTMCNF :=
  ntmFinalAcceptanceCNF M T.t

def instantiate
    {M : PolyNTMCandidate}
    (T : TableauTemplate M)
    (x : BitString) : NTMCNF :=
  templateInitial T x ++
  templateTransitions T x ++
  templateFinal T

/--
Exact factorization of the concrete bounded tableau through the
machine/length/time template. At this stage n records the layout class;
the current implementation's x-dependence in variable numbering has already
been proved length-only in SourceRecovery.
-/
@[simp] theorem boundedExec_factorization
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    boundedExecTableauCNF_NTM M x t =
      instantiate (tableauTemplate M x.length t) x := by
  rfl

@[simp] theorem template_radius
    (M : PolyNTMCandidate)
    (n t : Nat)
    (x : BitString)
    (h : x.length = n) :
    ntmRadius x t = n + t + 1 := by
  simp [ntmRadius, h]

end TableauTemplate
end Real
end MCore
