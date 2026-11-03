import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.PNPNTMTableauEncoding

namespace MCore
namespace Real
namespace P02TableauSourceRecovery

open CanonicalFinalProof
open CanonicalSATFrameAttack
open PNPNTMTableauEncoding

/-- R1: the canonical input tape is a lossless representation of the source
bitstring.  This is purely structural and uses the already-proved left inverse
`tapeWord_inputTape`. -/
theorem inputTape_injective :
    Function.Injective inputTape := by
  intro x y hxy
  have h := congrArg tapeWord hxy
  simpa using h

/-- The literal-to-circuit encoding preserves both the variable index and
polarity. -/
theorem ntmLiteralCircuit_injective :
    Function.Injective ntmLiteralCircuit := by
  intro a b h
  cases a with
  | mk av ap =>
      cases b with
      | mk bv bp =>
          cases ap <;> cases bp <;>
            simp [ntmLiteralCircuit] at h ⊢
          all_goals omega

/-- Clause encoding is injective because `or` is a constructor and the tail
is encoded recursively. -/
theorem ntmClauseCircuit_injective :
    Function.Injective ntmClauseCircuit := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons l ls =>
          simp [ntmClauseCircuit] at h
  | cons l ls ih =>
      intro b h
      cases b with
      | nil =>
          simp [ntmClauseCircuit] at h
      | cons k ks =>
          simp only [ntmClauseCircuit] at h
          injection h with hHead hTail
          have hl : l = k := ntmLiteralCircuit_injective hHead
          have hls : ls = ks := ih hTail
          subst k
          subst ks
          rfl

/-- R3: the CNF-to-circuit encoding is injective.  Hence wrapping a tableau
CNF in `ntmCNFCircuit` does not lose any CNF structure. -/
theorem ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons c cs =>
          simp [ntmCNFCircuit] at h
  | cons c cs ih =>
      intro b h
      cases b with
      | nil =>
          simp [ntmCNFCircuit] at h
      | cons d ds =>
          simp only [ntmCNFCircuit] at h
          injection h with hHead hTail
          have hc : c = d := ntmClauseCircuit_injective hHead
          have hcs : cs = ds := ih hTail
          subst d
          subst ds
          rfl

#print axioms MCore.Real.P02TableauSourceRecovery.inputTape_injective
#print axioms MCore.Real.P02TableauSourceRecovery.ntmLiteralCircuit_injective
#print axioms MCore.Real.P02TableauSourceRecovery.ntmClauseCircuit_injective
#print axioms MCore.Real.P02TableauSourceRecovery.ntmCNFCircuit_injective

end P02TableauSourceRecovery
end Real
end MCore
