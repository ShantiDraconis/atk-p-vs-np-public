import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace ClosedDiscriminant

structure StartAuditResult {Language : Type}
    (P NP : Language → Prop) : Prop where
  start : StartClosed P NP
  middle : MiddleClosed P NP
  finalEnvelope : FinalClosed P NP

theorem test_start_to_middle
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    MiddleClosed P NP :=
  (closed_chain hStart).1

theorem test_start_to_final_envelope
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    FinalClosed P NP :=
  (closed_chain hStart).2

theorem collect_start_result
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    StartAuditResult P NP :=
  ⟨hStart, test_start_to_middle hStart, test_start_to_final_envelope hStart⟩

#print axioms test_start_to_middle
#print axioms test_start_to_final_envelope
#print axioms collect_start_result

end ClosedDiscriminant
end MCore
