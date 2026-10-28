import MCore.C11.BranchingCost

open MCore MCore.C9 MCore.C10 MCore.C11 MCore.CircuitK1 MCore.CircuitC2

def fixesOneFalse : Restriction
  | 1 => some false
  | _ => none

def showCase (name : String) (ρ : Restriction) (t : FormulaTree) : IO Unit := do
  let m := metrics 1 1 ρ t
  let pays : Bool := decide (m.payoffLhs < m.potentialBefore)
  IO.println s!"CASE={name}"
  IO.println s!"vars={m.varsBefore}->{m.varsAfter} delta={m.deltaVars}"
  IO.println s!"mu={m.muBefore}->{m.muAfter} delta={m.deltaMu}"
  IO.println s!"rank={m.rankBefore}->{m.rankAfter} delta={m.deltaRank}"
  IO.println s!"costBits={m.costBits} branchingCost={m.branchingCost}"
  IO.println s!"potential={m.potentialBefore}->{m.potentialAfter} lhs={m.payoffLhs}"
  IO.println s!"paysOff={pays}"

def main : IO Unit := do
  showCase "reducible_fix0_true" fixesZeroTrue reducibleExample
  showCase "one_input_free" leavesZeroFree oneInput
  showCase "or_fix0_true" fixesZeroTrue twoInputOr
  showCase "or_fix1_false" fixesOneFalse twoInputOr
