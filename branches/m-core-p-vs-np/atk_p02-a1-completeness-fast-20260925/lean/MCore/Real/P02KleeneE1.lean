import MCore.Real.P02KleeneSelfReferenceBridge

namespace MCore
namespace Real
namespace P02KleeneE1

open CanonicalFinalProof
open P02KleeneSelfReferenceBridge

/-- E1 audit: the computable code-transformer component of the abstract
Kleene bridge is inhabited without any lower-bound assumption.  The identity
transformer suffices, so the remaining hardness cannot reside in
compile_computable. -/
def identityCompile
    (_M : PolyDTMCandidate)
    (c : Nat.Partrec.Code) :
    Nat.Partrec.Code :=
  c

theorem identityCompile_computable
    (M : PolyDTMCandidate) :
    Computable (identityCompile M) := by
  exact Computable.id

structure E1Compiler where
  compile : PolyDTMCandidate → Nat.Partrec.Code → Nat.Partrec.Code
  computable : ∀ M, Computable (compile M)

def identityE1Compiler : E1Compiler where
  compile := identityCompile
  computable := identityCompile_computable

theorem E1Compiler_nonempty :
    Nonempty E1Compiler :=
  ⟨identityE1Compiler⟩

#print axioms identityCompile_computable
#print axioms E1Compiler_nonempty

end P02KleeneE1
end Real
end MCore
