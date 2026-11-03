import MCore.Real.P01PreservingUnarySuccessorCycle

namespace MCore
namespace Real
namespace P01PreservingUnaryIteration

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnarySuccessorCycle
open MachineRunLemmas

/-- Sum of exact successor-cycle costs.  Only lengths matter. -/
def iteratedCycleFuelLen : Nat → Nat → Nat
  | _, 0 => 0
  | prefLen, movedLen + 1 =>
      (4 * prefLen + 8) + iteratedCycleFuelLen (prefLen + 1) movedLen

def iteratedCycleFuel (pref moved : BitString) : Nat :=
  iteratedCycleFuelLen pref.length moved.length

@[simp] theorem iteratedCycleFuel_nil
    (pref : BitString) :
    iteratedCycleFuel pref [] = 0 := rfl

theorem iteratedCycleFuel_cons
    (pref : BitString) (b : Bool) (rest : BitString) :
    iteratedCycleFuel pref (b :: rest) =
      successorCycleFuel pref +
        iteratedCycleFuel (pref ++ [b]) rest := by
  simp [iteratedCycleFuel, iteratedCycleFuelLen, successorCycleFuel]

/-- Iterating the exact one-cycle law moves the marker across every bit in
moved, preserving the remaining suffix and decreasing the unary index by
exactly moved.length. -/
theorem preservingRead_iterated_cycles
    (a : Bool) (seed moved suffix : BitString) (n : Nat)
    (hcount : moved.length ≤ n) :
    preservingUnaryReadMachine.run
        (iteratedCycleFuel (a :: seed) moved)
        (indexSomeConfig (a :: seed) (moved ++ suffix) n) =
      indexSomeConfig ((a :: seed) ++ moved) suffix (n - moved.length) := by
  induction moved generalizing a seed n with
  | nil =>
      simp [iteratedCycleFuel, iteratedCycleFuelLen, TM.run]
  | cons b rest ih =>
      have hn : 0 < n := by
        have hpos : 0 < (b :: rest).length := by simp
        omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have hrest : rest.length ≤ k := by
        simpa using hcount
      have hcycle :=
        preservingRead_indexSome_one_cycle a b seed (rest ++ suffix) k
      have hih :=
        ih (a := a) (seed := seed ++ [b]) (n := k) hrest
      have hfuel :
          iteratedCycleFuel (a :: seed) (b :: rest) =
            successorCycleFuel (a :: seed) +
              iteratedCycleFuel ((a :: seed) ++ [b]) rest := by
        exact iteratedCycleFuel_cons (a :: seed) b rest
      rw [hfuel]
      calc
        preservingUnaryReadMachine.run
            (successorCycleFuel (a :: seed) +
              iteratedCycleFuel ((a :: seed) ++ [b]) rest)
            (indexSomeConfig (a :: seed) ((b :: rest) ++ suffix) (k + 1))
            =
          preservingUnaryReadMachine.run
            (iteratedCycleFuel ((a :: seed) ++ [b]) rest)
            (preservingUnaryReadMachine.run
              (successorCycleFuel (a :: seed))
              (indexSomeConfig (a :: seed) (b :: (rest ++ suffix)) (k + 1))) := by
                rw [run_add]
                rfl
        _ =
          preservingUnaryReadMachine.run
            (iteratedCycleFuel ((a :: seed) ++ [b]) rest)
            (indexSomeConfig ((a :: seed) ++ [b]) (rest ++ suffix) k) := by
              rw [hcycle]
        _ =
          indexSomeConfig (((a :: seed) ++ [b]) ++ rest)
            suffix (k - rest.length) := by
              exact hih
        _ =
          indexSomeConfig ((a :: seed) ++ (b :: rest))
            suffix ((k + 1) - (b :: rest).length) := by
              simp [List.append_assoc]

#print axioms MCore.Real.P01PreservingUnaryIteration.preservingRead_iterated_cycles

end P01PreservingUnaryIteration
end Real
end MCore
