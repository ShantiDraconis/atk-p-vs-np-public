import P02.LANE4.StructuralClosure

namespace P02
namespace LANE4
namespace AUX
namespace STRUCTURAL_CLOSURE

abbrev StructuralClosure := P02.LANE4.StructuralClosure
abbrev structuralClosure := P02.LANE4.structuralClosure
abbrev T10_OPEN_MATH := P02.LANE4.T10_OPEN_MATH

theorem structural_closure_inhabited :
    Nonempty StructuralClosure :=
  ⟨structuralClosure⟩

#print axioms P02.LANE4.AUX.STRUCTURAL_CLOSURE.structural_closure_inhabited

end STRUCTURAL_CLOSURE
end AUX
end LANE4
end P02
