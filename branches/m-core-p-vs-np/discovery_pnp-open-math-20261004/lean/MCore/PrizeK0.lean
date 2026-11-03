import MCore.K10

namespace MCore

/-- Epistemic classification for the prize-focused algorithms-to-lower-bounds campaign. -/
inductive PrizeStatus where
  | provedInfrastructure
  | openAlgorithmicGap
  | openTransferGap
  deriving DecidableEq, Repr

/-- A deliberately minimal interface for a circuit class and its SAT decision problem.
    No complexity-theoretic separation is encoded in these fields. -/
structure CircuitSATInterface where
  Circuit : Type
  satisfiable : Circuit → Prop

/-- K-PRIZE K0 records only the research boundary that has been certified:
    there are distinct algorithmic and transfer obligations. It does not assert
    that either obligation has a solution. -/
structure PrizeCampaignBoundary where
  algorithmicGap : PrizeStatus := .openAlgorithmicGap
  transferGap : PrizeStatus := .openTransferGap

namespace PrizeCampaignBoundary

def canonical : PrizeCampaignBoundary := {}

@[simp] theorem canonical_algorithmic_open :
    canonical.algorithmicGap = .openAlgorithmicGap := rfl

@[simp] theorem canonical_transfer_open :
    canonical.transferGap = .openTransferGap := rfl

end PrizeCampaignBoundary

/-- The new campaign is fail-closed: merely introducing its interface cannot
    promote the previously open classical endpoint. -/
theorem prize_k0_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

/-- Nor does the campaign boundary manufacture the K10 witness whose existence
    would be substantive mathematical content. -/
theorem prize_k0_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  k10_not_certified

end MCore
