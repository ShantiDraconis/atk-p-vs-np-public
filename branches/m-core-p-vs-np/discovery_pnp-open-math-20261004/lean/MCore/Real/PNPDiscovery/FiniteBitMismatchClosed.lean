import MCore.Real.PNPDiscovery.SourceMismatchEncodingDichotomy

namespace MCore
namespace Real
namespace PNPDiscovery

/-- Pure finite-list fact closing the last generic mismatch bridge. -/
theorem unequalBitstringsSeparate_closed :
    UnequalBitstringsSeparate := by
  intro a
  induction a with
  | nil =>
      intro b hneq
      cases b with
      | nil =>
          exact False.elim (hneq rfl)
      | cons b bs =>
          left
          simp
  | cons a as ih =>
      intro b hneq
      cases b with
      | nil =>
          left
          simp
      | cons b bs =>
          by_cases hLen : as.length = bs.length
          · by_cases hHead : a = b
            · have hTail : as ≠ bs := by
                intro h
                apply hneq
                simp [hHead, h]
              rcases ih bs hTail with hLenDiff | hBit
              · exact False.elim (hLenDiff hLen)
              · right
                rcases hBit with ⟨q, hq, hdiff⟩
                refine ⟨q + 1, ?_, ?_⟩
                · simp [hLen] at hq ⊢
                  omega
                · simpa [List.getD_cons_succ] using hdiff
            · right
              refine ⟨0, ?_, ?_⟩
              · simp
              · simpa [List.getD_cons_zero] using hHead
          · left
            simp
            exact hLen

/-- Therefore the source-mismatch encoding dichotomy is CLOSED. -/
theorem sourceMismatchEncodingDichotomy_closed :
    SourceMismatchEncodingDichotomy :=
  unequalBitstringsSeparate_closes_sourceEncoding
    unequalBitstringsSeparate_closed

#print axioms MCore.Real.PNPDiscovery.unequalBitstringsSeparate_closed
#print axioms MCore.Real.PNPDiscovery.sourceMismatchEncodingDichotomy_closed

end PNPDiscovery
end Real
end MCore
