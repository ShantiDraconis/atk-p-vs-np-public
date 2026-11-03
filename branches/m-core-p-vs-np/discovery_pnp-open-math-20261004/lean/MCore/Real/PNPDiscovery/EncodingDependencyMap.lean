import MCore.Real.PNPDiscovery.PrefixPressure
import MCore.Real.CanonicalSATWitness
import MCore.Real.PNPNTMTableauEncoding

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open PNPNTMTableauEncoding
open P02ComplementRunRealization
open P02TableauDynamics
open P03PerfectFlipConstruction

/-- Exact unary length law, re-exported into the discovery namespace. -/
theorem encodeNat_exact_length
    (n : Nat) :
    (encodeNat n).length = n + 1 :=
  encodeNat_length n

/-- Every encoded natural is exactly n true bits followed by one false bit. -/
theorem encodeNat_eq_replicate
    (n : Nat) :
    encodeNat n = List.replicate n true ++ [false] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [encodeNat, ih, List.replicate_succ, List.append_assoc]

/-- Exact encoded length for an input node. -/
theorem encodeCircuit_input_length
    (i : Nat) :
    (encodeCircuit (.input i)).length = i + 4 := by
  simp [encodeCircuit, encodeNat_exact_length]
  omega

@[simp] theorem encodeCircuit_const_false_length :
    (encodeCircuit (.const false)).length = 3 := by
  rfl

@[simp] theorem encodeCircuit_const_true_length :
    (encodeCircuit (.const true)).length = 3 := by
  rfl

theorem encodeCircuit_not_length
    (c : CircuitK1.Circuit) :
    (encodeCircuit (.not c)).length =
      3 + (encodeCircuit c).length := by
  simp [encodeCircuit]

theorem encodeCircuit_and_length
    (a b : CircuitK1.Circuit) :
    (encodeCircuit (.and a b)).length =
      3 + (encodeCircuit a).length + (encodeCircuit b).length := by
  simp [encodeCircuit, Nat.add_assoc]

theorem encodeCircuit_or_length
    (a b : CircuitK1.Circuit) :
    (encodeCircuit (.or a b)).length =
      3 + (encodeCircuit a).length + (encodeCircuit b).length := by
  simp [encodeCircuit, Nat.add_assoc]

/-- Exact root tag of a nonempty CNF encoding. -/
theorem encode_ntmCNFCircuit_cons_prefix
    (c : NTMClause)
    (cs : NTMCNF) :
    ∃ tail : BitString,
      encodeCircuit (ntmCNFCircuit (c :: cs)) =
        [true, false, false] ++ tail := by
  refine ⟨
    encodeCircuit (ntmClauseCircuit c) ++
      encodeCircuit (ntmCNFCircuit cs), ?_⟩
  rfl

/-- The first three bits of every nonempty CNF encoding are exactly 100. -/
theorem encode_ntmCNFCircuit_cons_take3
    (c : NTMClause)
    (cs : NTMCNF) :
    (encodeCircuit (ntmCNFCircuit (c :: cs))).take 3 =
      [true, false, false] := by
  simp [ntmCNFCircuit, encodeCircuit]

/-- The real tableau CNF is nonempty, hence its reduction encoding has root
tag 100 before any source-dependent payload is inspected. -/
theorem reduction_take3_exact
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    (R_M M hTotal x).take 3 = [true, false, false] := by
  rcases R_M_fixed_prefix M hTotal x with ⟨tail, h⟩
  simp [h]

/-- A concrete polynomial envelope extracted from a candidate's stored
PolynomialTimeBound witness. -/
structure ClockEnvelope (M : PolyDTMCandidate) where
  coefficient : Nat
  exponent : Nat
  bound : ∀ n : Nat,
    M.timeBound n ≤ coefficient * (n + 1) ^ exponent

noncomputable def clockEnvelope
    (M : PolyDTMCandidate) :
    ClockEnvelope M := by
  classical
  rcases M.time_poly with ⟨c, k, h⟩
  exact
    { coefficient := c
      exponent := k
      bound := h }

/-- This is a genuine unpacking theorem, not new mathematics. -/
theorem timeBound_le_clockEnvelope
    (M : PolyDTMCandidate)
    (n : Nat) :
    M.timeBound n ≤
      (clockEnvelope M).coefficient *
        (n + 1) ^ (clockEnvelope M).exponent :=
  (clockEnvelope M).bound n

#print axioms MCore.Real.PNPDiscovery.encodeNat_eq_replicate
#print axioms MCore.Real.PNPDiscovery.encodeCircuit_input_length
#print axioms MCore.Real.PNPDiscovery.encode_ntmCNFCircuit_cons_take3
#print axioms MCore.Real.PNPDiscovery.reduction_take3_exact
#print axioms MCore.Real.PNPDiscovery.timeBound_le_clockEnvelope

end PNPDiscovery
end Real
end MCore
