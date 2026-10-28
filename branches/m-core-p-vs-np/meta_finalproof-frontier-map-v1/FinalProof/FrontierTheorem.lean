namespace FinalProof

/-- P01 boundary theorem: the current target cannot close while its required
construction obligation is absent. This is not a proof of P != NP. -/
structure P01Frontier (A P B : Prop) where
  prefixWitness : A
  missing : ¬ P
  targetRequires : B → P

theorem p01_target_unreachable
    {A P B : Prop} (f : P01Frontier A P B) : ¬ B := by
  intro hB
  exact f.missing (f.targetRequires hB)

/-- Literal G2.1 fixed-point route: closed formulation, not OPEN_BRIDGE. -/
structure G21LiteralFixedPointClosed (A A' PAlleged : Prop) where
  incompatible : A → ¬ A'
  closed : A ∧ PAlleged → False

theorem g21_literal_route_closed
    {A A' PAlleged : Prop}
    (f : G21LiteralFixedPointClosed A A' PAlleged)
    (hA : A) (hP : PAlleged) : False :=
  f.closed ⟨hA, hP⟩

end FinalProof
