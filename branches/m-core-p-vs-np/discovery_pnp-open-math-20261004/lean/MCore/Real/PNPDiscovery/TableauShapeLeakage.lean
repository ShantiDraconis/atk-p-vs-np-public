import MCore.Real.PNPDiscovery.LayoutAlphaEquivalence
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace PNPDiscovery

open PNPNTMTableauEncoding
open SourceRecovery

/-- Renaming variable IDs preserves the number of CNF clauses exactly. -/
@[simp] theorem renameCNF_length
    (ρ : Nat → Nat)
    (F : NTMCNF) :
    (renameCNF ρ F).length = F.length := by
  simp [renameCNF]

/-- Exact clause count of the time-zero tableau region. -/
theorem ntmInitialCNF_length_exact
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    (ntmInitialCNF M x t).length =
      ntmStateCount M + 3 + 6 * ntmRadius x t := by
  unfold ntmInitialCNF
  simp [length_ntmSetStateClauses,
    length_ntmSetSymbolClauses,
    length_initial_left_block,
    length_initial_right_block]
  omega

/-- Different retained radii force different initial-CNF shapes. -/
theorem ntmInitialCNF_length_ne_of_radius_ne
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hRadius :
      ntmRadius x t ≠ ntmRadius y u) :
    (ntmInitialCNF M x t).length ≠
      (ntmInitialCNF M y u).length := by
  rw [ntmInitialCNF_length_exact,
      ntmInitialCNF_length_exact]
  omega

/-- Therefore no alpha-renaming can identify initial CNFs of different radius:
the obstacle is shape/cardinality, not variable names. -/
theorem no_initialCNF_alphaEquivalent_of_radius_ne
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hRadius :
      ntmRadius x t ≠ ntmRadius y u) :
    ¬ CNFAlphaEquivalent
      (ntmInitialCNF M x t)
      (ntmInitialCNF M y u) := by
  intro H
  rcases H with ⟨ρ, σ, hρ, hσ, hEq⟩
  have hLen := congrArg List.length hEq
  simp at hLen
  exact
    (ntmInitialCNF_length_ne_of_radius_ne
      M x y t u hRadius) hLen

/-- Layout-shape split for unequal input lengths.
Either the retained radius already changes, producing an alpha-invariant shape
difference in the initial CNF, or the radius is equal and the changed input
length is exactly compensated by a changed clock. -/
theorem unequalLength_radius_or_clockCompensation
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length ≠ y.length) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    ntmRadius x tx ≠ ntmRadius y ty ∨
      (ntmRadius x tx = ntmRadius y ty ∧ tx ≠ ty) := by
  dsimp
  by_cases hRadius :
      ntmRadius x (M.timeBound x.length) =
        ntmRadius y (M.timeBound y.length)
  · right
    refine ⟨hRadius, ?_⟩
    intro hClock
    unfold ntmRadius at hRadius
    omega
  · exact Or.inl hRadius

/-- In the radius-mismatch branch the initial tableau shape itself leaks the
layout, and this cannot be removed by alpha-renaming. -/
theorem unequalLength_radiusLeak_not_alpha
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hRadius :
      ntmRadius x (M.timeBound x.length) ≠
        ntmRadius y (M.timeBound y.length)) :
    ¬ CNFAlphaEquivalent
      (ntmInitialCNF
        (complementToNTMCandidate M)
        x (M.timeBound x.length))
      (ntmInitialCNF
        (complementToNTMCandidate M)
        y (M.timeBound y.length)) := by
  exact no_initialCNF_alphaEquivalent_of_radius_ne
    (complementToNTMCandidate M)
    x y
    (M.timeBound x.length)
    (M.timeBound y.length)
    hRadius

/-- The only layout branch not already killed by alpha-invariant shape leakage:
same radius despite unequal source lengths, which necessarily means clocks differ. -/
def EqualRadiusClockCompensationRegime
    (M : PolyDTMCandidate)
    (x y : BitString) : Prop :=
  x.length ≠ y.length ∧
  ntmRadius x (M.timeBound x.length) =
    ntmRadius y (M.timeBound y.length) ∧
  M.timeBound x.length ≠ M.timeBound y.length

#print axioms MCore.Real.PNPDiscovery.ntmInitialCNF_length_exact
#print axioms MCore.Real.PNPDiscovery.no_initialCNF_alphaEquivalent_of_radius_ne
#print axioms MCore.Real.PNPDiscovery.unequalLength_radius_or_clockCompensation
#print axioms MCore.Real.PNPDiscovery.unequalLength_radiusLeak_not_alpha

end PNPDiscovery
end Real
end MCore
