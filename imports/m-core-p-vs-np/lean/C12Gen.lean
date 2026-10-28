import MCore.C12.Families

open MCore MCore.C9 MCore.C11 MCore.C12 MCore.CircuitK1

def csvHeader : String :=
  "family,n,k,seed,width,restriction,alpha,beta,varsBefore,varsAfter,deltaVars,muBefore,muAfter,deltaMu,rankBefore,rankAfter,deltaRank,costBits,branchingCost,potentialBefore,potentialAfter,payoffLhs,paysOff"

def csvRow
    (family : String)
    (n k seed width : Nat)
    (restrictionLabel : String)
    (ρ : Restriction)
    (t : FormulaTree) : String :=
  let m := metrics 1 1 ρ t
  let pays := if m.payoffLhs < m.potentialBefore then "true" else "false"
  s!"{family},{n},{k},{seed},{width},{restrictionLabel},1,1,{m.varsBefore},{m.varsAfter},{m.deltaVars},{m.muBefore},{m.muAfter},{m.deltaMu},{m.rankBefore},{m.rankAfter},{m.deltaRank},{m.costBits},{m.branchingCost},{m.potentialBefore},{m.potentialAfter},{m.payoffLhs},{pays}"

def rowsForN (n : Nat) : List String :=
  let ks := List.range (n + 1)
  let deterministic :=
    ks.flatMap fun k =>
      [ csvRow "or_n" n k 0 0 "prefix_true" (fixPrefix k true) (orN n)
      , csvRow "and_n" n k 0 0 "prefix_false" (fixPrefix k false) (andN n)
      , csvRow "reducible_n" n k 0 0 "prefix_true" (fixPrefix k true) (reducibleN n)
      ]
  let randomRows :=
    (List.range 4).flatMap fun seed =>
      ks.map fun k =>
        csvRow "random_k_cnf" n k seed 3 "prefix_alternating"
          (fixPrefixAlternating k)
          (randomKCNF n (2 * n + 1) 3 seed)
  deterministic ++ randomRows

def csvLines : List String :=
  csvHeader :: ((List.range 12).flatMap fun i => rowsForN (i + 1))

def main : IO Unit := do
  for line in csvLines do
    IO.println line
