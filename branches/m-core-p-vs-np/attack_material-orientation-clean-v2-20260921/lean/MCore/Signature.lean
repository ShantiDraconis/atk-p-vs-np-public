namespace MCore

inductive SignatureStatus where
  | candidate
  | definitionInterface
  | provedProperty
  | refutedProperty
  | openBridge
  deriving DecidableEq, Repr

structure CriticalSignature (Object Value : Type) where
  observable : Object → Value
  target : Value → Prop
  status : SignatureStatus := .candidate

end MCore
