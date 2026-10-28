import MCore.Real.P02SameInputOnlyFrontier
import MCore.Real.P02BoundedOpenMathFalsification

namespace MCore
namespace Real
namespace P02SameInputCoreFalsification

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneBridge
open P02CookLevinFromBoundedExec
open P02SameInputOnlyFrontier
open P02BoundedOpenMathFalsification

/-- Any proposed SameInputTransport for the concrete Cook--Levin rejectCircuit
is impossible: Mathlib's Kleene fixed point supplies a code c satisfying the
transport premise, while rejectCircuit strictly increases the length of the
resulting bitstring. -/
theorem no_sameInputTransport
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) :
    ¬ Nonempty (SameInputTransport M K) := by
  intro h
  rcases h with ⟨S⟩
  let c := Classical.choose (kleene_fixed_point K)
  have hfixed : Nat.Partrec.Code.eval c = K.f c :=
    Classical.choose_spec (kleene_fixed_point K)
  let x : BitString := S.selfInput c
  have hsame :
      x = encodeCircuit (rejectCircuit M x) := by
    simpa [x] using S.same_input_of_fixed c hfixed
  have hlt :
      x.length < (encodeCircuit (rejectCircuit M x)).length :=
    rejectCircuit_strict_growth M x
  have hlen :
      x.length = (encodeCircuit (rejectCircuit M x)).length :=
    congrArg List.length hsame
  exact (Nat.ne_of_lt hlt) hlen

/-- Therefore the current SameInputCore structure has no inhabitant. -/
theorem not_SameInputCore :
    ¬ Nonempty SameInputCore := by
  rintro ⟨S⟩
  let M : PolyDTMCandidate :=
    { stateCount := 0
      machine :=
        { initial := 0
          blank := none
          transition := fun q a => (q, a, .stay)
          halting := fun _ => true }
      blank_none := rfl
      accepting := fun _ => false
      timeBound := fun _ => 0
      time_poly := by
        refine ⟨0, 0, ?_⟩
        intro n
        simp }
  exact no_sameInputTransport M (S.compiler M) ⟨S.transport M⟩

/-- The formerly advertised SameInputCoreGap is not OPEN_MATH: it is false. -/
theorem not_SameInputCoreGap :
    ¬ SameInputCoreGap := by
  intro h
  rcases h with ⟨S⟩
  exact not_SameInputCore ⟨S⟩

#print axioms MCore.Real.P02SameInputCoreFalsification.no_sameInputTransport
#print axioms MCore.Real.P02SameInputCoreFalsification.not_SameInputCore
#print axioms MCore.Real.P02SameInputCoreFalsification.not_SameInputCoreGap

end P02SameInputCoreFalsification
end Real
end MCore
