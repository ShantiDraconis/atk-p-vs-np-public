import MCore.Real.PNPDiscovery.EncodingDependencyMap

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open P02ComplementRunRealization
open P02TableauDynamics

/-- Exact k-bit prefix agreement across all real reduction outputs of one
candidate.  This is a measurable discovery quantity, not an endpoint. -/
def StablePrefixAt
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat) : Prop :=
  ∀ x y : BitString,
    (R_M M hTotal x).take k =
      (R_M M hTotal y).take k

theorem stablePrefix_zero
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    StablePrefixAt M hTotal 0 := by
  intro x y
  simp

theorem stablePrefix_three
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    StablePrefixAt M hTotal 3 := by
  intro x y
  rw [reduction_take3_exact M hTotal x]
  rw [reduction_take3_exact M hTotal y]

/-- Monotonicity: a stable longer prefix gives every shorter stable prefix. -/
theorem stablePrefix_mono
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    {j k : Nat}
    (hjk : j ≤ k)
    (hk : StablePrefixAt M hTotal k) :
    StablePrefixAt M hTotal j := by
  intro x y
  have h := congrArg (fun bs : BitString => bs.take j) (hk x y)
  simpa [List.take_take, Nat.min_eq_left hjk] using h

/-- Any nonempty clause circuit begins with the canonical OR tag 101. -/
theorem encode_ntmClauseCircuit_cons_take3
    (l : NTMLiteral)
    (ls : NTMClause) :
    (encodeCircuit (ntmClauseCircuit (l :: ls))).take 3 =
      [true, false, true] := by
  simp [ntmClauseCircuit, encodeCircuit]

/-- If the first CNF clause is nonempty, six leading bits are forced:
AND-root 100 followed by OR-root 101. -/
theorem encode_ntmCNFCircuit_nonempty_clause_take6
    (l : NTMLiteral)
    (ls : NTMClause)
    (cs : NTMCNF) :
    (encodeCircuit
      (ntmCNFCircuit ((l :: ls) :: cs))).take 6 =
      [true, false, false, true, false, true] := by
  simp [ntmCNFCircuit, ntmClauseCircuit, encodeCircuit]

/-- Exact one-bit extension question.  This is the local unit that the kernel
must settle when growing the stable prefix. -/
def PrefixExtensionObligation
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat) : Prop :=
  StablePrefixAt M hTotal k →
    StablePrefixAt M hTotal (k + 1)

theorem prefixExtension_success
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat)
    (H : PrefixExtensionObligation M hTotal k)
    (hk : StablePrefixAt M hTotal k) :
    StablePrefixAt M hTotal (k + 1) :=
  H hk

/-- Failure to extend a stable prefix produces two concrete reduction outputs
whose next prefixes differ.  No P/NP endpoint appears here. -/
theorem not_stablePrefix_exists_pair
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat)
    (h : ¬ StablePrefixAt M hTotal k) :
    ∃ x y : BitString,
      (R_M M hTotal x).take k ≠
        (R_M M hTotal y).take k := by
  classical
  unfold StablePrefixAt at h
  push_neg at h
  exact h

/-- If k is stable but k+1 is not, the first newly exposed disagreement is
localized exactly at the extension boundary. -/
def FirstUnstableExtension
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat) : Prop :=
  StablePrefixAt M hTotal k ∧
    ¬ StablePrefixAt M hTotal (k + 1)

theorem firstUnstableExtension_has_pair
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (k : Nat)
    (H : FirstUnstableExtension M hTotal k) :
    ∃ x y : BitString,
      (R_M M hTotal x).take k =
        (R_M M hTotal y).take k ∧
      (R_M M hTotal x).take (k + 1) ≠
        (R_M M hTotal y).take (k + 1) := by
  rcases not_stablePrefix_exists_pair M hTotal (k + 1) H.2 with
    ⟨x, y, hxy⟩
  exact ⟨x, y, H.1 x y, hxy⟩

#print axioms MCore.Real.PNPDiscovery.stablePrefix_three
#print axioms MCore.Real.PNPDiscovery.stablePrefix_mono
#print axioms MCore.Real.PNPDiscovery.encode_ntmCNFCircuit_nonempty_clause_take6
#print axioms MCore.Real.PNPDiscovery.not_stablePrefix_exists_pair
#print axioms MCore.Real.PNPDiscovery.firstUnstableExtension_has_pair

end PNPDiscovery
end Real
end MCore
