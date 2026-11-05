namespace Audit.SAT

def valuationBits {n : Nat} (v : Valuation n) : BitStr :=
  List.ofFn v

@[simp] theorem valuationBits_length {n : Nat} (v : Valuation n) :
    (valuationBits v).length = n := by
  simp [valuationBits]

def valuationOfExactBits {n : Nat}
    (w : BitStr) (h : w.length = n) : Valuation n :=
  fun i => w.get ⟨i.val, by simpa [h] using i.isLt⟩

@[simp] theorem valuationOfExactBits_valuationBits
    {n : Nat} (v : Valuation n) :
    valuationOfExactBits (valuationBits v) (valuationBits_length v) = v := by
  funext i
  simp [valuationOfExactBits, valuationBits]

def SATBitVerifier (φ : CNF) (w : BitStr) : Prop :=
  ∃ h : w.length = φ.nvars,
    evalCNF φ (valuationOfExactBits w h) = true

theorem satisfiable_iff_bitWitness (φ : CNF) :
    Satisfiable φ ↔ ∃ w : BitStr, SATBitVerifier φ w := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨valuationBits v, ?_⟩
    unfold SATBitVerifier
    refine ⟨valuationBits_length v, ?_⟩
    simpa using hv
  · rintro ⟨w, hw⟩
    rcases hw with ⟨hLen, hEval⟩
    exact ⟨valuationOfExactBits w hLen, hEval⟩

def SATBitWitnessSemantics (x : BitStr) : Prop :=
  ∃ φ : CNF,
    decodeCNF x = some φ ∧
      ∃ w : BitStr, SATBitVerifier φ w

theorem SATBits_iff_bitWitnessSemantics (x : BitStr) :
    SATBits concreteBitEncoding x ↔ SATBitWitnessSemantics x := by
  constructor
  · rintro ⟨φ, hdec, hsat⟩
    refine ⟨φ, ?_, (satisfiable_iff_bitWitness φ).mp hsat⟩
    exact hdec
  · rintro ⟨φ, hdec, hw⟩
    exact ⟨φ, hdec, (satisfiable_iff_bitWitness φ).mpr hw⟩

theorem SATBits_encodeCNF_iff (φ : CNF) :
    SATBits concreteBitEncoding (encodeCNF φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨ψ, hdec, hsat⟩
    change decodeCNF (encodeCNF φ) = some ψ at hdec
    rw [decodeCNF_encodeCNF] at hdec
    have hEq : φ = ψ := Option.some.inj hdec
    simpa [hEq] using hsat
  · intro hsat
    exact ⟨φ, decodeCNF_encodeCNF φ, hsat⟩

theorem decode_none_not_SATBits {x : BitStr}
    (h : decodeCNF x = none) :
    ¬ SATBits concreteBitEncoding x := by
  intro hs
  rcases hs with ⟨φ, hdec, _⟩
  change decodeCNF x = some φ at hdec
  rw [h] at hdec
  contradiction

/-- The exact operational residue after the semantic SAT witness layer.
No inhabitant is postulated here. -/
structure SATNTMRealization where
  machine : Audit.OfficialModel.NTM
  bound : Audit.OfficialModel.PolyBound
  decides :
    Audit.OfficialModel.NTM.DecidesWithin
      machine (SATBits concreteBitEncoding) bound

def SATNTMRealizationExistence : Prop :=
  Nonempty SATNTMRealization

theorem SATNTMRealization_implies_OfficialNP :
    SATNTMRealizationExistence →
      Audit.OfficialModel.OfficialNP (SATBits concreteBitEncoding) := by
  rintro ⟨R⟩
  exact ⟨R.machine, R.bound, R.decides⟩

def SATWitnessLayerStatus : String := "PROVED_INTERNAL"
def SATNTMRealizationStatus : String := "OPEN_BRIDGE_MACHINE_AND_POLYBOUND"

#print axioms Audit.SAT.valuationBits_length
#print axioms Audit.SAT.valuationOfExactBits_valuationBits
#print axioms Audit.SAT.satisfiable_iff_bitWitness
#print axioms Audit.SAT.SATBits_iff_bitWitnessSemantics
#print axioms Audit.SAT.SATBits_encodeCNF_iff
#print axioms Audit.SAT.decode_none_not_SATBits
#print axioms Audit.SAT.SATNTMRealization_implies_OfficialNP

end Audit.SAT
