namespace MCore.Hardening

inductive NodePolicy where
  | constructive
  | classical_ok
  deriving Repr, DecidableEq

inductive NodeStatus where
  | declared
  | derived
  | conditional
  | open_math
  | closed_by_falsification
  | rejected
  deriving Repr, DecidableEq

inductive RejectedReason where
  | sorryAx
  | new_axiom
  | type_mismatch
  | vacuous
  | circular
  | inconsistent_hypotheses
  | strawman
  | axiom_policy_mismatch
  deriving Repr, DecidableEq

/-- Closed declared base. Metadata only; mathematical force comes only from
actual Lean declarations and their `#print axioms` output. -/
def declaredBase : List Lean.Name :=
  [`propext, `Classical.choice, `Quot.sound]

structure NodePolicyRecord where
  node : String
  policy : NodePolicy
  allowedAxioms : List Lean.Name
  deriving Repr

def p01Policy : NodePolicyRecord :=
  { node := "P01"
    policy := .classical_ok
    allowedAxioms := declaredBase }

def ssePolicy : NodePolicyRecord :=
  { node := "SSE"
    policy := .classical_ok
    allowedAxioms := declaredBase }

def g21NegativePolicy : NodePolicyRecord :=
  { node := "G21_LITERAL_NEGATIVE"
    policy := .classical_ok
    allowedAxioms := declaredBase }

end MCore.Hardening
