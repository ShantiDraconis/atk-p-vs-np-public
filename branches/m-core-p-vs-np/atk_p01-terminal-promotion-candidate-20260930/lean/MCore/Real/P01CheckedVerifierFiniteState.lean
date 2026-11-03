import MCore.Real.P01CheckedVerifierStateCodec
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01CheckedVerifierFiniteState

open P01IntegratedAssembly
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierStateCodec

/-- Exact explicit control count obtained from the no-Mathlib codec. -/
def checkedVerifierStateCount : Nat := 1851

def checkedVerifierStateEncode
    (q : CheckedVerifierState) :
    Fin (checkedVerifierStateCount + 1) := by
  change Fin 1852
  simpa [checkedVerifierStateCodec_size] using
    checkedVerifierStateCodec.encode q

def checkedVerifierStateDecode
    (q : Fin (checkedVerifierStateCount + 1)) :
    CheckedVerifierState := by
  change Fin 1852 at q
  exact checkedVerifierStateCodec.decode
    (by simpa [checkedVerifierStateCodec_size] using q)

theorem checkedVerifierStateDecode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateDecode (checkedVerifierStateEncode q) = q := by
  simpa [checkedVerifierStateDecode, checkedVerifierStateEncode,
    checkedVerifierStateCount] using
      checkedVerifier_decode_encode q

/-- Concrete Fin-indexed checked verifier obtained only by control-state
relabeling. No transition, tape behavior, acceptance or rejection semantics
are changed. -/
def checkedVerifierFinMachine :
    NTM (Fin (checkedVerifierStateCount + 1)) (Option Bool) :=
  relabel
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode

@[simp] theorem checkedVerifierFinMachine_blank :
    checkedVerifierFinMachine.blank = none := rfl

theorem checkedVerifierFinMachine_haltsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.HaltsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.HaltsWithin n c := by
  exact relabel_haltsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

theorem checkedVerifierFinMachine_acceptsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.AcceptsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.AcceptsWithin n c := by
  exact relabel_acceptsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierStateDecode_encode
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_acceptsWithin_iff

end P01CheckedVerifierFiniteState
end Real
end MCore
