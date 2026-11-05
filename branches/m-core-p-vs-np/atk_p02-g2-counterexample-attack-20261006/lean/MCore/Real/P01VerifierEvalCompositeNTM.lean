import MCore.Real.P01FullVerifierSourceToStack
import MCore.Real.P01EvalRunLoopNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01VerifierEvalCompositeNTM

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierTraversal
open P01FullVerifierPhysicalShuttles
open P01FullVerifierPhysicalStackV2
open P01EvalCursorMachine
open P01EvalRunLoopNTM
open P01NTMRunLaws

/-- One fixed finite-control verifier core:
prepared source → source-end scan → empty physical eval stack → evalRun loop. -/
inductive VerifierEvalState where
  | start
  | scan : Fin 2 → VerifierEvalState
  | enter
  | eval : EvalRunLoopState → VerifierEvalState
  | reject
  deriving DecidableEq, Repr

abbrev VerifierEvalConfig :=
  Configuration VerifierEvalState (Option Bool)

def scanEmbed
    (c : Configuration (Fin 2) (Option Bool)) :
    VerifierEvalConfig :=
  { state := .scan c.state, tape := c.tape }

def evalStateEmbed : EvalRunLoopState → VerifierEvalState :=
  fun q => .eval q

/-- The concrete verifier core.  Empty source is rejected immediately.
Nonempty source is scanned exactly once before entering the global evaluator. -/
def verifierEvalMachine :
    NTM VerifierEvalState (Option Bool) where
  initial := .start
  blank := none
  transition := fun q symbol =>
    match q with
    | .start =>
        match symbol with
        | none => [(.reject, none, .stay)]
        | some b =>
            let t := sourceEndScanner.transition sourceEndScanner.initial (some b)
            [(.scan t.1, t.2.1, t.2.2)]
    | .scan qs =>
        if sourceEndScanner.halting qs then
          [(.enter, symbol, .stay)]
        else
          let t := sourceEndScanner.transition qs symbol
          [(.scan t.1, t.2.1, t.2.2)]
    | .enter =>
        [(.eval evalRunLoopMachine.initial, symbol, .right)]
    | .eval qe =>
        (evalRunLoopMachine.transition qe symbol).map
          (fun t => (.eval t.1, t.2.1, t.2.2))
    | .reject => []
  accepting := fun q =>
    match q with
    | .eval qe => evalRunLoopMachine.accepting qe
    | _ => false
  rejecting := fun q =>
    match q with
    | .eval qe => evalRunLoopMachine.rejecting qe
    | .reject => true
    | _ => false

@[simp] theorem verifierEvalMachine_initial :
    verifierEvalMachine.initial = .start := rfl

@[simp] theorem verifierEvalMachine_blank :
    verifierEvalMachine.blank = none := rfl

@[simp] theorem start_not_halted (tape : Tape (Option Bool)) :
    ¬ Halted verifierEvalMachine
      ({ state := .start, tape := tape } : VerifierEvalConfig) := by
  simp [Halted, verifierEvalMachine]

@[simp] theorem scanEmbed_not_halted
    (c : Configuration (Fin 2) (Option Bool)) :
    ¬ Halted verifierEvalMachine (scanEmbed c) := by
  simp [Halted, scanEmbed, verifierEvalMachine]

@[simp] theorem enter_not_halted (tape : Tape (Option Bool)) :
    ¬ Halted verifierEvalMachine
      ({ state := .enter, tape := tape } : VerifierEvalConfig) := by
  simp [Halted, verifierEvalMachine]

/-- Active deterministic scanner steps embed exactly as singleton verifier
successors. -/
theorem scan_successors_active
    (c : Configuration (Fin 2) (Option Bool))
    (h : sourceEndScanner.halting c.state = false) :
    verifierEvalMachine.successors (scanEmbed c) =
      [scanEmbed (sourceEndScanner.step c)] := by
  unfold NTM.successors
  simp [scanEmbed, verifierEvalMachine, h, NTM.stepBranch, TM.step,
    Tape.write, Tape.move]

private theorem one_step_of_successor
    (a b : VerifierEvalConfig)
    (ha : ¬ Halted verifierEvalMachine a)
    (hs : b ∈ verifierEvalMachine.successors a) :
    b ∈ verifierEvalMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      verifierEvalMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- A finite deterministic scanner run is reachable inside the verifier with
the same fuel. -/
theorem scan_run_reachable :
    ∀ (n : Nat) (c : Configuration (Fin 2) (Option Bool)),
      ∃ m ≤ n,
        scanEmbed (sourceEndScanner.run n c) ∈
          verifierEvalMachine.runBranches m [scanEmbed c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change scanEmbed c ∈ [scanEmbed c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : sourceEndScanner.halting c.state with
      | true =>
          have hr := MachineRunLemmas.run_halted
            sourceEndScanner c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (sourceEndScanner.step c)
          have hsucc :
              scanEmbed (sourceEndScanner.step c) ∈
                verifierEvalMachine.successors (scanEmbed c) := by
            rw [scan_successors_active c hhalt]
            simp
          have hone :
              scanEmbed (sourceEndScanner.step c) ∈
                verifierEvalMachine.runBranches 1 [scanEmbed c] :=
            one_step_of_successor
              (scanEmbed c) (scanEmbed (sourceEndScanner.step c))
              (scanEmbed_not_halted c) hsucc
          have htrans :=
            mem_runBranches_trans verifierEvalMachine
              1 m [scanEmbed c]
              (scanEmbed (sourceEndScanner.step c))
              (scanEmbed (sourceEndScanner.run n (sourceEndScanner.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

/-- A nonempty prepared verifier tape reaches the canonical evaluator start
layout in at most source.length+3 wrapper steps. -/
theorem prepared_nonempty_reaches_eval_start
    (witness : BitString) (b : Bool) (bs : BitString) :
    ∃ m ≤ (b :: bs).length + 3,
      ({ state := .eval evalRunLoopMachine.initial,
         tape :=
           evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
        VerifierEvalConfig) ∈
      verifierEvalMachine.runBranches m
        [{ state := verifierEvalMachine.initial,
           tape := preparedTape witness (b :: bs) }] := by
  let cStart : VerifierEvalConfig :=
    { state := .start, tape := preparedTape witness (b :: bs) }
  let cScan0 : Configuration (Fin 2) (Option Bool) :=
    scanConfig (some b :: none :: witness.map some) bs
  let cScanH : Configuration (Fin 2) (Option Bool) :=
    { state := (1 : Fin 2), tape := sourceEndTape witness (b :: bs) }
  let cEnter : VerifierEvalConfig :=
    { state := .enter, tape := sourceEndTape witness (b :: bs) }
  let cEval : VerifierEvalConfig :=
    { state := .eval evalRunLoopMachine.initial,
      tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }

  have hStartSucc :
      scanEmbed cScan0 ∈ verifierEvalMachine.successors cStart := by
    dsimp [cStart, cScan0, scanEmbed]
    cases b <;> cases bs <;>
      simp [verifierEvalMachine, NTM.successors, NTM.stepBranch,
        sourceEndScanner, scanConfig, preparedTape,
        TM.step, Tape.write, Tape.move, List.append_assoc]
  have hStart :
      scanEmbed cScan0 ∈ verifierEvalMachine.runBranches 1 [cStart] :=
    one_step_of_successor cStart (scanEmbed cScan0)
      (by dsimp [cStart]; exact start_not_halted _) hStartSucc

  have hScanExact :
      sourceEndScanner.run (bs.length + 1) cScan0 = cScanH := by
    dsimp [cScan0, cScanH]
    rw [sourceEndScanner_run]
    simp [sourceEndTape, List.reverse_cons, List.map_append,
      List.append_assoc]

  obtain ⟨mS, hmS, hS⟩ :=
    scan_run_reachable (bs.length + 1) cScan0
  have hS' :
      scanEmbed cScanH ∈
        verifierEvalMachine.runBranches mS [scanEmbed cScan0] := by
    rw [hScanExact] at hS
    exact hS
  have hToScan :=
    mem_runBranches_trans verifierEvalMachine
      1 mS [cStart] (scanEmbed cScan0) (scanEmbed cScanH)
      hStart hS'

  have hScanHandSucc :
      cEnter ∈ verifierEvalMachine.successors (scanEmbed cScanH) := by
    dsimp [cEnter, cScanH, scanEmbed]
    simp [verifierEvalMachine, NTM.successors, NTM.stepBranch,
      sourceEndScanner, sourceEndTape, Tape.write, Tape.move]
  have hScanHand :
      cEnter ∈ verifierEvalMachine.runBranches 1 [scanEmbed cScanH] :=
    one_step_of_successor (scanEmbed cScanH) cEnter
      (scanEmbed_not_halted cScanH) hScanHandSucc
  have hToEnter :=
    mem_runBranches_trans verifierEvalMachine
      (1 + mS) 1 [cStart] (scanEmbed cScanH) cEnter
      hToScan hScanHand

  have hEnterSucc :
      cEval ∈ verifierEvalMachine.successors cEnter := by
    dsimp [cEval, cEnter]
    unfold NTM.successors
    simp [verifierEvalMachine, NTM.stepBranch,
      sourceEndTape, evalCursorStackEndTape,
      Tape.write, Tape.move, List.reverse_cons,
      List.map_append, List.append_assoc]
  have hEnter :
      cEval ∈ verifierEvalMachine.runBranches 1 [cEnter] :=
    one_step_of_successor cEnter cEval
      (by dsimp [cEnter]; exact enter_not_halted _) hEnterSucc

  have hAll :=
    mem_runBranches_trans verifierEvalMachine
      ((1 + mS) + 1) 1 [cStart] cEnter cEval hToEnter hEnter
  refine ⟨((1 + mS) + 1) + 1, ?_, ?_⟩
  · dsimp [cStart] at hAll ⊢
    omega
  · dsimp [cStart, cEval] at hAll ⊢
    simpa [verifierEvalMachine] using hAll

/-- Empty prepared source is rejected immediately, so total verifier handling
does not rely on circuit decoding being valid. -/
theorem prepared_empty_reaches_reject
    (witness : BitString) :
    ({ state := .reject, tape := preparedTape witness [] } :
      VerifierEvalConfig) ∈
      verifierEvalMachine.runBranches 1
        [{ state := verifierEvalMachine.initial,
           tape := preparedTape witness [] }] := by
  let c0 : VerifierEvalConfig :=
    { state := .start, tape := preparedTape witness [] }
  let cr : VerifierEvalConfig :=
    { state := .reject, tape := preparedTape witness [] }
  have hs : cr ∈ verifierEvalMachine.successors c0 := by
    dsimp [c0, cr]
    simp [verifierEvalMachine, preparedTape,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have h :=
    one_step_of_successor c0 cr
      (by dsimp [c0]; exact start_not_halted _) hs
  simpa [c0, cr, verifierEvalMachine] using h

/-- The whole evalRun NTM embeds exactly inside the verifier core. -/
def evalSimulation :
    P01NTMRunLaws.Simulation
      evalRunLoopMachine verifierEvalMachine evalStateEmbed where
  accepting := by
    intro q
    rfl
  rejecting := by
    intro q
    rfl
  successors := by
    intro c hactive
    rcases c with ⟨q, tape⟩
    cases q <;>
      simp [Halted, evalStateEmbed, verifierEvalMachine,
        evalRunLoopMachine, P01NTMRunLaws.liftConfig,
        NTM.successors, NTM.stepBranch, List.map_map,
        Function.comp_def, Tape.write, Tape.move] at hactive ⊢

theorem eval_runBranches_map
    (n : Nat)
    (xs : List (Configuration EvalRunLoopState (Option Bool))) :
    verifierEvalMachine.runBranches n
      (xs.map (P01NTMRunLaws.liftConfig evalStateEmbed)) =
    (evalRunLoopMachine.runBranches n xs).map
      (P01NTMRunLaws.liftConfig evalStateEmbed) :=
  P01NTMRunLaws.runBranches_map
    evalRunLoopMachine verifierEvalMachine
      evalStateEmbed evalSimulation n xs

#print axioms MCore.Real.P01VerifierEvalCompositeNTM.prepared_nonempty_reaches_eval_start
#print axioms MCore.Real.P01VerifierEvalCompositeNTM.prepared_empty_reaches_reject
#print axioms MCore.Real.P01VerifierEvalCompositeNTM.evalSimulation
#print axioms MCore.Real.P01VerifierEvalCompositeNTM.eval_runBranches_map

end P01VerifierEvalCompositeNTM
end Real
end MCore
