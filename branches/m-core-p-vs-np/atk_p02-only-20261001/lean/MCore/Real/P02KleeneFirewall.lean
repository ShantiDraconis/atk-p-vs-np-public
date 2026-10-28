import MCore.Real.P02KleeneKernel

namespace MCore
namespace Real
namespace P02KleeneFirewall

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02KleeneKernel

abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/--
A SAT fixed-point realizer is impossible for a candidate that is correct on
every canonical SAT input.  Hence the realizer is not a free consequence of
Kleene's recursion theorem: it already carries the material semantic defeat
of the candidate.
-/
theorem no_fixedPointRealizer_of_global_correctness
    (M : PolyDTMCandidate)
    (hCorrect : ∀ x : BitString, M.CorrectAt SATTarget x)
    (K : EffectiveDiagonalCompiler M) :
    ¬ Nonempty (SATFixedPointRealizer M K) := by
  rintro ⟨R⟩
  rcases kleene_fixed_point K with ⟨c, hc⟩
  let x : BitString := R.bitsOf c
  have hflip : SATTarget x ↔ ¬ DeclaredAccept M x :=
    R.flip_of_fixed c hc
  exact (fixed_flip_fails M x hflip) (hCorrect x)

/--
Consequently, if canonical SAT is in P, no uniform Kleene/SAT bridge can be
inhabited.  This is the precise firewall against treating the recursion
theorem as if it alone supplied the lower bound.
-/
theorem inP_excludes_kleeneSATBridgeGap
    (hP : InP SATTarget) :
    ¬ KleeneSATBridgeGap := by
  intro hBridge
  exact (kleene_bridge_closes_not_in_p hBridge) hP

/--
Equivalent contrapositive presentation used by the P02 audit.
-/
theorem kleeneSATBridgeGap_is_material_lower_bound
    (hBridge : KleeneSATBridgeGap) :
    ¬ InP SATTarget :=
  kleene_bridge_closes_not_in_p hBridge

#print axioms MCore.Real.P02KleeneFirewall.no_fixedPointRealizer_of_global_correctness
#print axioms MCore.Real.P02KleeneFirewall.inP_excludes_kleeneSATBridgeGap
#print axioms MCore.Real.P02KleeneFirewall.kleeneSATBridgeGap_is_material_lower_bound

end P02KleeneFirewall
end Real
end MCore
