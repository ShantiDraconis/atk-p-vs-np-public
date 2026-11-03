import MCore.Real.P02FiniteClockNormalization
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02FiniteCandidateDescription

open CanonicalFinalProof
open CanonicalCircuitBits
open P02FiniteClockNormalization

def encodeBool : Bool → BitString
  | false => [false]
  | true => [true]

def encodeOptionBool : Option Bool → BitString
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def encodeDirection : Direction → BitString
  | .left => [false, false]
  | .stay => [false, true]
  | .right => [true, false]

def encodeState {n : Nat} (q : Fin (n + 1)) : BitString :=
  encodeNat q.val

def encodeTransitionEntry
    {n : Nat}
    (q : Fin (n + 1))
    (a : Option Bool)
    (tr : Fin (n + 1) × Option Bool × Direction) : BitString :=
  encodeState q ++
  encodeOptionBool a ++
  encodeState tr.1 ++
  encodeOptionBool tr.2.1 ++
  encodeDirection tr.2.2

def transitionTable
    (M : PolyDTMCandidate) :
    List (Fin (M.stateCount + 1) × Option Bool ×
      (Fin (M.stateCount + 1) × Option Bool × Direction)) :=
  (List.ofFn fun q : Fin (M.stateCount + 1) => q).flatMap fun q =>
    [none, some false, some true].map fun a =>
      (q, a, M.machine.transition q a)

def acceptingTable
    (M : PolyDTMCandidate) :
    List (Fin (M.stateCount + 1) × Bool) :=
  (List.ofFn fun q : Fin (M.stateCount + 1) => q).map fun q =>
    (q, M.accepting q)

def encodeTransitionTable
    (M : PolyDTMCandidate) : BitString :=
  (transitionTable M).flatMap fun e =>
    encodeTransitionEntry e.1 e.2.1 e.2.2

def encodeAcceptingTable
    (M : PolyDTMCandidate) : BitString :=
  (acceptingTable M).flatMap fun e =>
    encodeState e.1 ++ encodeBool e.2

noncomputable def candidateCode
    (M : PolyDTMCandidate) : BitString :=
  encodeNat M.stateCount ++
  encodeState M.machine.initial ++
  encodeTransitionTable M ++
  encodeAcceptingTable M ++
  encodeNat (clockCoeff M) ++
  encodeNat (clockExp M)

theorem transitionTable_complete
    (M : PolyDTMCandidate)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    (q, a, M.machine.transition q a) ∈ transitionTable M := by
  unfold transitionTable
  rw [List.mem_flatMap]
  have hq :
      q ∈ List.ofFn (fun i : Fin (M.stateCount + 1) => i) := by
    exact List.mem_ofFn.mpr ⟨q, rfl⟩
  refine ⟨q, hq, ?_⟩
  cases a with
  | none => simp
  | some b =>
      cases b <;> simp

theorem acceptingTable_complete
    (M : PolyDTMCandidate)
    (q : Fin (M.stateCount + 1)) :
    (q, M.accepting q) ∈ acceptingTable M := by
  unfold acceptingTable
  have hq :
      q ∈ List.ofFn (fun i : Fin (M.stateCount + 1) => i) := by
    exact List.mem_ofFn.mpr ⟨q, rfl⟩
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

theorem candidateCode_finite
    (M : PolyDTMCandidate) :
    ∃ bits : BitString, bits = candidateCode M := by
  exact ⟨candidateCode M, rfl⟩

#print axioms MCore.Real.P02FiniteCandidateDescription.transitionTable_complete
#print axioms MCore.Real.P02FiniteCandidateDescription.acceptingTable_complete
#print axioms MCore.Real.P02FiniteCandidateDescription.candidateCode_finite

end P02FiniteCandidateDescription
end Real
end MCore
