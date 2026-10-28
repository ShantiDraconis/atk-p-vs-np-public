import MCore.Real.P02_YangMills.SourceBinding

namespace MCore.Real.P02_YangMills.OpenBridge.B60Target

open P02_YangMills.SourceBinding

/-- Source-bound real frontier for the current Yang-Mills lane.
This records the canonical external type; it does not re-declare the foreign
Lean structure locally. -/
def targetName : String := "Nonempty (B60ConcretePhysicalAdapter C F D H G O)"

def sourceRepo : String := canonicalYMRepo
def sourceRef : String := canonicalYMRef
def sourcePath : String := "lean/MCore/YangMills/A1/B60ConcretePhysicalAdapter.lean"
def sourceTheorem : String := "B60ConcretePhysicalOpenBridge / B60ConcretePhysicalAdapter"

theorem source_ref_fixed :
    sourceRef = "cd4bbfd348b607bd24ed0c6d605207b764286f58" := rfl

#print axioms MCore.Real.P02_YangMills.OpenBridge.B60Target.source_ref_fixed

end MCore.Real.P02_YangMills.OpenBridge.B60Target
