import MCore.Real.P02G21FinalNegative

namespace MCore
namespace Real
namespace G21TransferCandidateEngine

/-- Canonical operator order used by the transversal inventory:
U, B, R, N, C, F, Z, P, I. -/
structure Signature where
  U : Bool
  B : Bool
  R : Bool
  N : Bool
  C : Bool
  F : Bool
  Z : Bool
  P : Bool
  I : Bool
deriving DecidableEq, Repr

def hamming (a b : Signature) : Nat :=
  (if a.U = b.U then 0 else 1) +
  (if a.B = b.B then 0 else 1) +
  (if a.R = b.R then 0 else 1) +
  (if a.N = b.N then 0 else 1) +
  (if a.C = b.C then 0 else 1) +
  (if a.F = b.F then 0 else 1) +
  (if a.Z = b.Z then 0 else 1) +
  (if a.P = b.P then 0 else 1) +
  (if a.I = b.I then 0 else 1)

/-- Integer form of D_struct < 0.2 for nine Boolean coordinates:
distance/9 < 1/5 iff 5*distance < 9. -/
def structurallyClose (a b : Signature) : Bool :=
  decide (5 * hamming a b < 9)

structure TransferTarget where
  source : Signature
  target : Signature
  hypothesisCompatible : Bool
  operatorInstantiated : Bool

/-- Fail-closed transfer candidate.  Structural similarity alone is
insufficient; both exact hypothesis compatibility and operator instantiation
must also be certified. -/
def transfer_candidate_from_G21 (t : TransferTarget) : Bool :=
  structurallyClose t.source t.target &&
    t.hypothesisCompatible &&
    t.operatorInstantiated

theorem no_transfer_without_hypothesis_compatibility
    (t : TransferTarget)
    (h : t.hypothesisCompatible = false) :
    transfer_candidate_from_G21 t = false := by
  simp [transfer_candidate_from_G21, h]

theorem no_transfer_without_operator
    (t : TransferTarget)
    (h : t.operatorInstantiated = false) :
    transfer_candidate_from_G21 t = false := by
  simp [transfer_candidate_from_G21, h]

theorem no_transfer_from_distance_alone
    (t : TransferTarget)
    (hclose : structurallyClose t.source t.target = true)
    (hhyp : t.hypothesisCompatible = false) :
    transfer_candidate_from_G21 t = false := by
  simp [transfer_candidate_from_G21, hclose, hhyp]

#print axioms MCore.Real.G21TransferCandidateEngine.no_transfer_without_hypothesis_compatibility
#print axioms MCore.Real.G21TransferCandidateEngine.no_transfer_without_operator
#print axioms MCore.Real.G21TransferCandidateEngine.no_transfer_from_distance_alone

end G21TransferCandidateEngine
end Real
end MCore
