
import MCore.Real.PNPCookLevinMaterialMinCut

namespace MCore
namespace Real
namespace PNPNTMTableauFrontier

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open CircuitK1
open PNPCookLevinMaterialMinCut

/--
Exact nondeterministic Cook--Levin tableau producer.

The circuit must be CNF and must characterize acceptance of the supplied
canonical NTM within the supplied fuel.  No P/NP endpoint occurs in the type.
-/
structure NTMTableauProducer where
  circuit :
    PolyNTMCandidate -> BitString -> Nat -> Circuit
  isCNF :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      IsCNF (circuit M x t)
  correctness :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      SATLanguage (circuit M x t) <->
        M.machine.AcceptsWithin t
          (initialNTMConfig M.machine x)
  coefficient :
    PolyNTMCandidate -> Nat
  exponent :
    PolyNTMCandidate -> Nat
  encoded_length_le :
    forall (M : PolyNTMCandidate) (x : BitString) (t : Nat),
      (encodeCircuit (circuit M x t)).length <=
        coefficient M * (x.length + t + 1) ^ exponent M

/--
A genuine NTM tableau producer immediately gives the semantic part of the
canonical SAT reduction for every concrete NP realization.
-/
def NTMTableauProducer.toSemanticReduction
    (P : NTMTableauProducer)
    {L : BitLanguage}
    (R : PolyNTMRealization L) :
    NTMToCanonicalSATSemanticReduction R where
  reduce := fun x =>
    encodeCircuit
      (P.circuit R.candidate x
        (R.candidate.timeBound x.length))
  correct := by
    intro x
    have hdec := R.decides x
    have hsem :
        R.candidate.machine.AcceptsWithin
            (R.candidate.timeBound x.length)
            (initialNTMConfig R.candidate.machine x) <->
          L x :=
      hdec.2
    calc
      L x
          <-> R.candidate.machine.AcceptsWithin
                (R.candidate.timeBound x.length)
                (initialNTMConfig R.candidate.machine x) := hsem.symm
      _ <-> SATLanguage
              (P.circuit R.candidate x
                (R.candidate.timeBound x.length)) :=
            (P.correctness R.candidate x
              (R.candidate.timeBound x.length)).symm
      _ <-> CanonicalSAT
              (encodeCircuit
                (P.circuit R.candidate x
                  (R.candidate.timeBound x.length))) :=
            (encoded_sat_equivalence
              (P.circuit R.candidate x
                (R.candidate.timeBound x.length))).symm

/--
The universal semantic reduction atom is therefore no longer mysterious:
its sole mathematical source is an inhabitant of NTMTableauProducer.
-/
def semanticMaterializer_of_ntmTableau
    (P : NTMTableauProducer) :
    forall {L : BitLanguage} (R : PolyNTMRealization L),
      NTMToCanonicalSATSemanticReduction R :=
  fun R => P.toSemanticReduction R

def PNP_NTM_TABLEAU_OPEN_MATH : Prop :=
  Nonempty NTMTableauProducer

#print axioms MCore.Real.PNPNTMTableauFrontier.NTMTableauProducer.toSemanticReduction
#print axioms MCore.Real.PNPNTMTableauFrontier.semanticMaterializer_of_ntmTableau

end PNPNTMTableauFrontier
end Real
end MCore
