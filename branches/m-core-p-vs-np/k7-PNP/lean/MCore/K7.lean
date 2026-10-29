import MCore.K6

namespace MCore

/-- K7 audit reachability over the frozen K6 dependency.
    This is an audit certificate, not a proof of P vs NP. -/
inductive K7Reachable : CertNode → CertNode → Prop
  | dependency : K7Reachable k6_dependency.source k6_dependency.target

theorem k7_dependency_reachable :
    K7Reachable k6_dependency.source k6_dependency.target :=
  K7Reachable.dependency

theorem k7_source_open :
    k6_dependency.source.status = .openBridge :=
  k6_source_open

theorem k7_target_open :
    k6_dependency.target.status = .openBridge :=
  k6_target_open

theorem k7_target_not_certified :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

end MCore
