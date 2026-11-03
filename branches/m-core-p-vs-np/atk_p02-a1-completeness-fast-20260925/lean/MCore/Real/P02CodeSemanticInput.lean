import Mathlib.Computability.PartrecCode
import MCore.Real.P02BitStringNatCoding

namespace MCore
namespace Real
namespace P02CodeSemanticInput

open P02BitStringNatCoding

/-- Total semantic projection from a partial-recursive program code to a
bitstring.  We observe the program at the distinguished input 0.  If the
program is undefined there, the canonical default is the empty bitstring. -/
noncomputable def selfInput (c : Nat.Partrec.Code) :
    CanonicalFinalProof.BitString := by
  classical
  exact if h : (c.eval 0).Dom then
    decodeBitsNatD ((c.eval 0).get h)
  else
    []

/-- The projection depends only on program semantics, not on syntax. -/
theorem selfInput_ext
    (a b : Nat.Partrec.Code)
    (hEval : a.eval = b.eval) :
    selfInput a = selfInput b := by
  have h0 : a.eval 0 = b.eval 0 := congrFun hEval 0
  classical
  unfold selfInput
  rw [h0]

/-- A code whose value at zero is the natural encoding of x projects back to
exactly x. -/
theorem selfInput_of_mem_encode
    (c : Nat.Partrec.Code)
    (x : CanonicalFinalProof.BitString)
    (hmem : encodeBitsNat x ∈ c.eval 0) :
    selfInput c = x := by
  classical
  unfold selfInput
  have hdom : (c.eval 0).Dom := (Part.dom_iff_mem).2 ⟨encodeBitsNat x, hmem⟩
  rw [dif_pos hdom]
  have hget : (c.eval 0).get hdom = encodeBitsNat x :=
    Part.get_eq_of_mem hmem hdom
  rw [hget]
  exact decodeBitsNatD_encodeBitsNat x

#print axioms MCore.Real.P02CodeSemanticInput.selfInput_ext
#print axioms MCore.Real.P02CodeSemanticInput.selfInput_of_mem_encode

end P02CodeSemanticInput
end Real
end MCore
