import MCore.C12.Families

open MCore MCore.C9 MCore.C11 MCore.C12 MCore.CircuitK1

def probeHeader : String :=
  "family,n,k,seed,width,restriction,alpha,beta,varsBefore,varsAfter,deltaVars,muBefore,muAfter,deltaMu,rankBefore,rankAfter,deltaRank,costBits,branchingCost,potentialBefore,potentialAfter,payoffLhs,paysOff"

def probeRow
    (family : String)
    (n k seed width : Nat)
    (restrictionLabel : String)
    (ρ : Restriction)
    (t : FormulaTree) : String :=
  let m := metrics 1 1 ρ t
  let pays := if m.payoffLhs < m.potentialBefore then "true" else "false"
  s!"{family},{n},{k},{seed},{width},{restrictionLabel},1,1,{m.varsBefore},{m.varsAfter},{m.deltaVars},{m.muBefore},{m.muAfter},{m.deltaMu},{m.rankBefore},{m.rankAfter},{m.deltaRank},{m.costBits},{m.branchingCost},{m.potentialBefore},{m.potentialAfter},{m.payoffLhs},{pays}"

def probeRowsForN (n : Nat) : List String :=
  [0, 1].flatMap fun k =>
    let deterministic :=
      [ probeRow "or_n" n k 0 0 "prefix_true" (fixPrefix k true) (orN n)
      , probeRow "and_n" n k 0 0 "prefix_false" (fixPrefix k false) (andN n)
      , probeRow "reducible_n" n k 0 0 "prefix_true" (fixPrefix k true) (reducibleN n)
      ]
    let randomRows :=
      (List.range 8).map fun seed =>
        probeRow "random_k_cnf" n k seed 3 "prefix_alternating"
          (fixPrefixAlternating k)
          (randomKCNF n (2 * n + 1) 3 seed)
    deterministic ++ randomRows

def probeLines : List String :=
  probeHeader ::
    ((List.range 52).flatMap fun i => probeRowsForN (i + 13))

def main : IO Unit := do
  for line in probeLines do
    IO.println line
