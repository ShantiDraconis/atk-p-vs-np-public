import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace OfficialModel

open CanonicalFinalProof

/-- External complexity-model contract.

The witness types are intentionally external to the hardened internal
PolyDTM/PolyNTM realizations. A concrete external model must provide these
witness types together with explicit source provenance. This file never
identifies the external model with InP/InNP by definition. -/
structure OfficialComplexityModel where
  PRealization : BitLanguage → Type
  NPRealization : BitLanguage → Type

def OfficialComplexityModel.P
    (M : OfficialComplexityModel) :
    BitLanguage → Prop :=
  fun L => Nonempty (M.PRealization L)

def OfficialComplexityModel.NP
    (M : OfficialComplexityModel) :
    BitLanguage → Prop :=
  fun L => Nonempty (M.NPRealization L)

/-- Provenance required before a model can participate in G3.

These fields are data, not proof of semantic equivalence. The nonempty
conditions prevent an unlabeled internal alias from being promoted as an
external/official model. -/
structure OfficialModelSource where
  statement : String
  repository : String
  namespaceName : String
  sourceFile : String
  closureCondition : String
  statement_nonempty : statement ≠ ""
  repository_nonempty : repository ≠ ""
  namespace_nonempty : namespaceName ≠ ""
  sourceFile_nonempty : sourceFile ≠ ""
  closureCondition_nonempty : closureCondition ≠ ""

/-- One explicitly selected external model plus its normative source record. -/
structure OfficialModelSelection where
  model : OfficialComplexityModel
  source : OfficialModelSource

def OfficialModelSelected : Prop :=
  Nonempty OfficialModelSelection

end OfficialModel
end Real
end MCore
