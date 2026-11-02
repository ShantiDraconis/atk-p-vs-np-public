import MCore.Real.P01ManualStateCodecComposite
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01CheckedVerifierManualFiniteState

open P01CheckedVerifierCompositeNTM
open P01ManualStateCodecComposite
open P01IntegratedAssembly

/-- Exact number of encoded checked-verifier states.
The target Fin type has one additional unreachable spare code. -/
def checkedVerifierStateCount : Nat := 1852

def checkedVerifierCode : CheckedVerifierState → Nat
  | .start => 0
  | .scan q => 1 + q.val
  | .enter => 3
  | .eval q => 4 + checkedEvalCode q
  | .reject => 1851

def checkedVerifierDecode (n : Nat) : CheckedVerifierState :=
  if n = 0 then .start
  else if n = 1 then .scan ⟨0, by decide⟩
  else if n = 2 then .scan ⟨1, by decide⟩
  else if n = 3 then .enter
  else if n < 1851 then .eval (checkedEvalDecode (n - 4))
  else .reject

@[simp] theorem checkedVerifierDecode_code
    (q : CheckedVerifierState) :
    checkedVerifierDecode (checkedVerifierCode q) = q := by
  cases q with
  | start =>
      simp [checkedVerifierDecode, checkedVerifierCode]
  | scan q =>
      rcases q with ⟨n, hn⟩
      cases n with
      | zero =>
          rfl
      | succ n =>
          cases n with
          | zero =>
              rfl
          | succ n =>
              omega
  | enter =>
      simp [checkedVerifierDecode, checkedVerifierCode]
  | eval q =>
      have h := checkedEvalCode_lt q
      unfold checkedEvalStateCount at h
      have h0 : 4 + checkedEvalCode q ≠ 0 := by omega
      have h1 : 4 + checkedEvalCode q ≠ 1 := by omega
      have h2 : 4 + checkedEvalCode q ≠ 2 := by omega
      have h3 : 4 + checkedEvalCode q ≠ 3 := by omega
      have h1851 : 4 + checkedEvalCode q < 1851 := by omega
      have hsub : 4 + checkedEvalCode q - 4 = checkedEvalCode q := by omega
      simp [checkedVerifierDecode, checkedVerifierCode, h0, h1, h2, h3, h1851,
        hsub, checkedEvalDecode_code]
  | reject =>
      simp [checkedVerifierDecode, checkedVerifierCode]

theorem checkedVerifierCode_lt
    (q : CheckedVerifierState) :
    checkedVerifierCode q < checkedVerifierStateCount := by
  cases q with
  | start => decide
  | scan q =>
      have h := q.isLt
      simp [checkedVerifierCode, checkedVerifierStateCount]
      omega
  | enter => decide
  | eval q =>
      have h := checkedEvalCode_lt q
      unfold checkedEvalStateCount at h
      unfold checkedVerifierStateCount
      change 4 + checkedEvalCode q < 1852
      omega
  | reject => decide

def checkedVerifierStateEncode
    (q : CheckedVerifierState) :
    Fin (checkedVerifierStateCount + 1) :=
  ⟨checkedVerifierCode q, by
    exact Nat.lt_succ_of_lt (checkedVerifierCode_lt q)⟩

def checkedVerifierStateDecode
    (q : Fin (checkedVerifierStateCount + 1)) :
    CheckedVerifierState :=
  checkedVerifierDecode q.val

theorem checkedVerifierStateDecode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateDecode (checkedVerifierStateEncode q) = q :=
  checkedVerifierDecode_code q

/-- Concrete Fin-indexed checked verifier obtained only by state relabelling.
No tape transition or acceptance semantics are changed. -/
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

#print axioms MCore.Real.P01CheckedVerifierManualFiniteState.checkedVerifierDecode_code
#print axioms MCore.Real.P01CheckedVerifierManualFiniteState.checkedVerifierStateDecode_encode
#print axioms MCore.Real.P01CheckedVerifierManualFiniteState.checkedVerifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01CheckedVerifierManualFiniteState.checkedVerifierFinMachine_acceptsWithin_iff

end P01CheckedVerifierManualFiniteState
end Real
end MCore
