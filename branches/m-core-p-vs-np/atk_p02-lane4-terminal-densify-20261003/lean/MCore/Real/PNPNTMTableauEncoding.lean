import Mathlib.Tactic
import MCore.Real.PNPNTMPathFrontier

namespace MCore
namespace Real
namespace PNPNTMTableauEncoding

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMPathFrontier

structure NTMLiteral where
  var : Nat
  positive : Bool
  deriving DecidableEq, Repr

abbrev NTMClause := List NTMLiteral

abbrev NTMCNF := List NTMClause

def ntmPos (v : Nat) : NTMLiteral := { var := v, positive := true }

def ntmNeg (v : Nat) : NTMLiteral := { var := v, positive := false }

def ntmLiteralCircuit (l : NTMLiteral) : Circuit :=
  if l.positive then .input l.var else .not (.input l.var)

def ntmClauseCircuit : NTMClause -> Circuit
  | [] => .const false
  | l :: ls => .or (ntmLiteralCircuit l) (ntmClauseCircuit ls)

def ntmCNFCircuit : NTMCNF -> Circuit
  | [] => .const true
  | c :: cs => .and (ntmClauseCircuit c) (ntmCNFCircuit cs)

def evalNTMLiteral (sigma : Assignment) (l : NTMLiteral) : Bool :=
  if l.positive then sigma l.var else !(sigma l.var)

def evalNTMClause (sigma : Assignment) : NTMClause -> Bool
  | [] => false
  | l :: ls => Bool.or (evalNTMLiteral sigma l) (evalNTMClause sigma ls)

def evalNTMCNF (sigma : Assignment) : NTMCNF -> Bool
  | [] => true
  | c :: cs => Bool.and (evalNTMClause sigma c) (evalNTMCNF sigma cs)

def ntmAlphabet : List (Option Bool) :=
  [none, some false, some true]

def ntmSymbolCode : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

def ntmRadius (x : BitString) (t : Nat) : Nat :=
  x.length + t + 1

def ntmStateCount (M : PolyNTMCandidate) : Nat :=
  M.stateCount + 1

def ntmStateSlots (M : PolyNTMCandidate) (t : Nat) : Nat :=
  (t + 1) * ntmStateCount M

def ntmHeadBase (M : PolyNTMCandidate) (t : Nat) : Nat :=
  ntmStateSlots M t

def ntmLeftBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmHeadBase M t + (t + 1) * 3

def ntmRightBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmLeftBase M x t + (t + 1) * ntmRadius x t * 3

def ntmChoiceBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmRightBase M x t + (t + 1) * ntmRadius x t * 3

def ntmStateVar
    (M : PolyNTMCandidate) (t s : Nat)
    (q : Fin (M.stateCount + 1)) : Nat :=
  s * ntmStateCount M + q.val

def ntmHeadVar
    (M : PolyNTMCandidate) (t s : Nat)
    (a : Option Bool) : Nat :=
  ntmHeadBase M t + s * 3 + ntmSymbolCode a

def ntmLeftVar
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  ntmLeftBase M x t +
    (s * ntmRadius x t + i) * 3 + ntmSymbolCode a

def ntmRightVar
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  ntmRightBase M x t +
    (s * ntmRadius x t + i) * 3 + ntmSymbolCode a

def ntmBranchBound (M : PolyNTMCandidate) : Nat :=
  (((List.ofFn fun q : Fin (M.stateCount + 1) => q).flatMap fun q =>
      ntmAlphabet.map fun a => (M.machine.transition q a).length)).foldl Nat.max 0

def ntmChoiceVar
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) (j : Nat) : Nat :=
  ntmChoiceBase M x t +
    ((((s * ntmStateCount M + q.val) * 3 + ntmSymbolCode a) *
      (ntmBranchBound M + 1)) + j)

def ntmLitFor (v : Nat) (value : Bool) : NTMLiteral :=
  if value then ntmPos v else ntmNeg v

def ntmSetStateClauses
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) : NTMCNF :=
  List.ofFn fun q : Fin (M.stateCount + 1) =>
    guard ++ [ntmLitFor (ntmStateVar M t s q) (decide (q = target))]

def ntmSetSymbolClauses
    (guard : NTMClause)
    (varAt : Option Bool -> Nat)
    (target : Option Bool) : NTMCNF :=
  ntmAlphabet.map fun a =>
    guard ++ [ntmLitFor (varAt a) (decide (a = target))]

def ntmCopySymbolClauses
    (guard : NTMClause)
    (oldVar newVar : Option Bool -> Nat) : NTMCNF :=
  ntmAlphabet.flatMap fun a =>
    [ guard ++ [ntmNeg (oldVar a), ntmPos (newVar a)]
    , guard ++ [ntmPos (oldVar a), ntmNeg (newVar a)] ]

def ntmCopyLeftAll
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.range (ntmRadius x t)).flatMap fun i =>
    ntmCopySymbolClauses guard
      (ntmLeftVar M x t s i)
      (ntmLeftVar M x t (s + 1) i)

def ntmCopyRightAll
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.range (ntmRadius x t)).flatMap fun i =>
    ntmCopySymbolClauses guard
      (ntmRightVar M x t s i)
      (ntmRightVar M x t (s + 1) i)

def ntmSetLeftCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : NTMCNF :=
  ntmSetSymbolClauses guard (ntmLeftVar M x t s i) target

def ntmSetRightCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : NTMCNF :=
  ntmSetSymbolClauses guard (ntmRightVar M x t s i) target

def ntmCopyLeftCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmLeftVar M x t oldS oldI)
    (ntmLeftVar M x t newS newI)

def ntmCopyRightCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmRightVar M x t oldS oldI)
    (ntmRightVar M x t newS newI)

def ntmCopyHeadCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (t oldS newS : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmHeadVar M t oldS)
    (ntmHeadVar M t newS)

def ntmInitialCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  let tape := inputTape x
  ntmSetStateClauses [] M t 0 M.machine.initial ++
  ntmSetSymbolClauses [] (ntmHeadVar M t 0) tape.head ++
  (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetLeftCell [] M x t 0 i
      (tape.left.getD i M.machine.blank)) ++
  (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetRightCell [] M x t 0 i
      (tape.right.getD i M.machine.blank))

def ntmIndexedTransitionsAux
    {State Symbol : Type} :
    Nat -> List (State × Symbol × Direction) ->
      List (Nat × (State × Symbol × Direction))
  | _, [] => []
  | j, tr :: rest => (j, tr) :: ntmIndexedTransitionsAux (j + 1) rest

def ntmIndexedTransitions
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction)) :
    List (Nat × (State × Symbol × Direction)) :=
  ntmIndexedTransitionsAux 0 ts

def ntmChoiceGuardCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) (j : Nat) : NTMCNF :=
  let c := ntmChoiceVar M x t s q a j
  [ [ntmNeg c, ntmPos (ntmStateVar M t s q)]
  , [ntmNeg c, ntmPos (ntmHeadVar M t s a)] ]

def ntmGuardChoiceClause
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMClause :=
  [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)] ++
    (ntmIndexedTransitions (M.machine.transition q a)).map
      (fun p => ntmPos (ntmChoiceVar M x t s q a p.1))

def ntmAtMostOneChoiceCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let ids := (ntmIndexedTransitions (M.machine.transition q a)).map Prod.fst
  ids.flatMap fun j =>
    ids.flatMap fun k =>
      if j < k then
        [[ntmNeg (ntmChoiceVar M x t s q a j),
          ntmNeg (ntmChoiceVar M x t s q a k)]]
      else []

def ntmStayEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmSetSymbolClauses guard (ntmHeadVar M t (s + 1)) write ++
  ntmCopyLeftAll guard M x t s ++
  ntmCopyRightAll guard M x t s

def ntmLeftEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  let r := ntmRadius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyLeftCell guard M x t s (i + 1) (s + 1) i
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyRightCell guard M x t s i (s + 1) (i + 1)
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmCopySymbolClauses guard
    (ntmLeftVar M x t s 0)
    (ntmHeadVar M t (s + 1)) ++
  shiftedLeft ++
  ntmSetLeftCell guard M x t (s + 1) (r - 1) M.machine.blank ++
  ntmSetRightCell guard M x t (s + 1) 0 write ++
  shiftedRight

def ntmRightEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  let r := ntmRadius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyLeftCell guard M x t s i (s + 1) (i + 1)
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyRightCell guard M x t s (i + 1) (s + 1) i
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmCopySymbolClauses guard
    (ntmRightVar M x t s 0)
    (ntmHeadVar M t (s + 1)) ++
  ntmSetLeftCell guard M x t (s + 1) 0 write ++
  shiftedLeft ++
  shiftedRight ++
  ntmSetRightCell guard M x t (s + 1) (r - 1) M.machine.blank

def ntmChoiceEffectCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction)) : NTMCNF :=
  let j := entry.1
  let tr := entry.2
  let guard := [ntmNeg (ntmChoiceVar M x t s q a j)]
  match tr with
  | (qNext, write, .stay) =>
      ntmStayEffectCNF guard M x t s qNext write
  | (qNext, write, .left) =>
      ntmLeftEffectCNF guard M x t s qNext write
  | (qNext, write, .right) =>
      ntmRightEffectCNF guard M x t s qNext write

def ntmHaltedStutterCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let guard := [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  ntmSetStateClauses guard M t (s + 1) q ++
  ntmCopyHeadCell guard M t s (s + 1) ++
  ntmCopyLeftAll guard M x t s ++
  ntmCopyRightAll guard M x t s

def ntmActiveChoiceCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  [ntmGuardChoiceClause M x t s q a] ++
  entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
  ntmAtMostOneChoiceCNF M x t s q a ++
  entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)

def ntmTransitionCaseCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  if M.machine.accepting q || M.machine.rejecting q then
    ntmHaltedStutterCNF M x t s q a
  else
    ntmActiveChoiceCNF M x t s q a

def ntmTransitionStepCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.ofFn fun q : Fin (M.stateCount + 1) =>
    ntmAlphabet.flatMap fun a =>
      ntmTransitionCaseCNF M x t s q a).flatten

def ntmTransitionsCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  (List.range t).flatMap fun s =>
    ntmTransitionStepCNF M x t s

def ntmAcceptingStateLits
    (M : PolyNTMCandidate) (t : Nat) : NTMClause :=
  (List.ofFn fun q : Fin (M.stateCount + 1) => q).filterMap fun q =>
    if M.machine.accepting q = true then
      some (ntmPos (ntmStateVar M t t q))
    else none

def ntmFinalAcceptanceCNF
    (M : PolyNTMCandidate) (t : Nat) : NTMCNF :=
  [ntmAcceptingStateLits M t]

def boundedExecTableauCNF_NTM
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  ntmInitialCNF M x t ++
  ntmTransitionsCNF M x t ++
  ntmFinalAcceptanceCNF M t

def boundedExecCircuit_NTM
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Circuit :=
  ntmCNFCircuit (boundedExecTableauCNF_NTM M x t)

theorem evalNTMCNF_append
    (sigma : Assignment) (l1 l2 : NTMCNF) :
    evalNTMCNF sigma (l1 ++ l2) = true <->
      evalNTMCNF sigma l1 = true ∧
      evalNTMCNF sigma l2 = true := by
  induction l1 with
  | nil =>
      simp [evalNTMCNF]
  | cons c cs ih =>
      simp only [List.cons_append, evalNTMCNF, Bool.and_eq_true]
      rw [ih]
      constructor
      · rintro ⟨hc, hcs, hl2⟩
        exact ⟨⟨hc, hcs⟩, hl2⟩
      · rintro ⟨⟨hc, hcs⟩, hl2⟩
        exact ⟨hc, hcs, hl2⟩

theorem evalNTMCNF_cons_iff
    (sigma : Assignment) (c : NTMClause) (cs : NTMCNF) :
    evalNTMCNF sigma (c :: cs) = true <->
      evalNTMClause sigma c = true ∧
      evalNTMCNF sigma cs = true := by
  simp [evalNTMCNF, Bool.and_eq_true]

theorem evalNTMCNF_of_mem
    (sigma : Assignment) (f : NTMCNF) (c : NTMClause)
    (hSat : evalNTMCNF sigma f = true)
    (hc : c ∈ f) :
    evalNTMClause sigma c = true := by
  induction f with
  | nil =>
      simp at hc
  | cons d ds ih =>
      have hsplit :
          evalNTMClause sigma d = true ∧
          evalNTMCNF sigma ds = true :=
        (evalNTMCNF_cons_iff sigma d ds).mp hSat
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hsplit.1
      · exact ih hsplit.2 hc

@[simp] theorem evalNTMClause_singleton_pos
    (sigma : Assignment) (v : Nat) :
    evalNTMClause sigma [ntmPos v] = true <->
      sigma v = true := by
  cases h : sigma v <;>
    simp [evalNTMClause, evalNTMLiteral, ntmPos, h]

@[simp] theorem evalNTMClause_singleton_neg
    (sigma : Assignment) (v : Nat) :
    evalNTMClause sigma [ntmNeg v] = true <->
      sigma v = false := by
  cases h : sigma v <;>
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, h]

theorem eval_ntmLiteralCircuit
    (sigma : Assignment) (l : NTMLiteral) :
    evalCircuit sigma (ntmLiteralCircuit l) = evalNTMLiteral sigma l := by
  cases l with
  | mk v p =>
      cases p <;> rfl

theorem eval_ntmClauseCircuit
    (sigma : Assignment) (c : NTMClause) :
    evalCircuit sigma (ntmClauseCircuit c) = evalNTMClause sigma c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      simp [ntmClauseCircuit, evalCircuit, evalNTMClause,
        eval_ntmLiteralCircuit, ih]

theorem eval_ntmCNFCircuit
    (sigma : Assignment) (f : NTMCNF) :
    evalCircuit sigma (ntmCNFCircuit f) = evalNTMCNF sigma f := by
  induction f with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [ntmCNFCircuit, evalCircuit, evalNTMCNF,
        eval_ntmClauseCircuit, ih]

theorem ntmLiteralCircuit_isClause (l : NTMLiteral) :
    IsClause (ntmLiteralCircuit l) := by
  cases l with
  | mk v p =>
      cases p <;> simp [ntmLiteralCircuit, IsClause]

theorem ntmClauseCircuit_isClause (c : NTMClause) :
    IsClause (ntmClauseCircuit c) := by
  induction c with
  | nil => exact emptyClause_isClause
  | cons l ls ih =>
      exact IsClause_or (ntmLiteralCircuit_isClause l) ih

theorem ntmCNFCircuit_isCNF (f : NTMCNF) :
    IsCNF (ntmCNFCircuit f) := by
  induction f with
  | nil => exact emptyCNF_isCNF
  | cons c cs ih =>
      exact IsCNF_and (isClause_isCNF (ntmClauseCircuit_isClause c)) ih

theorem satLanguage_ntmCNFCircuit_iff
    (f : NTMCNF) :
    SATLanguage (ntmCNFCircuit f) <->
      ∃ sigma : Assignment, evalNTMCNF sigma f = true := by
  constructor
  · rintro ⟨_hcnf, sigma, hsat⟩
    exact ⟨sigma, by simpa [eval_ntmCNFCircuit] using hsat⟩
  · rintro ⟨sigma, hsat⟩
    refine ⟨ntmCNFCircuit_isCNF f, sigma, ?_⟩
    simpa [eval_ntmCNFCircuit] using hsat

@[simp] theorem evalNTMClause_singleton_litFor
    (sigma : Assignment) (v : Nat) (b : Bool) :
    evalNTMClause sigma [ntmLitFor v b] = true <->
      sigma v = b := by
  cases b <;>
    simp [ntmLitFor]

theorem evalNTMCNF_ofFn_litFor_iff
    {n : Nat}
    (sigma : Assignment)
    (v : Fin n -> Nat)
    (b : Fin n -> Bool) :
    evalNTMCNF sigma
        (List.ofFn fun i : Fin n => [ntmLitFor (v i) (b i)]) = true <->
      forall i : Fin n, sigma (v i) = b i := by
  induction n with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      rw [evalNTMCNF_cons_iff]
      rw [evalNTMClause_singleton_litFor]
      constructor
      · rintro ⟨h0, hs⟩ i
        refine Fin.cases h0 ?_ i
        intro j
        exact (ih
          (fun k => v k.succ)
          (fun k => b k.succ)).mp hs j
      · intro h
        constructor
        · exact h 0
        · exact (ih
            (fun k => v k.succ)
            (fun k => b k.succ)).mpr
            (fun j => h j.succ)

theorem eval_ntmSetStateClauses_nil_iff
    (sigma : Assignment)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    evalNTMCNF sigma (ntmSetStateClauses [] M t s target) = true <->
      forall q : Fin (M.stateCount + 1),
        sigma (ntmStateVar M t s q) = decide (q = target) := by
  simpa [ntmSetStateClauses] using
    (evalNTMCNF_ofFn_litFor_iff
      sigma
      (fun q : Fin (M.stateCount + 1) => ntmStateVar M t s q)
      (fun q : Fin (M.stateCount + 1) => decide (q = target)))

theorem eval_ntmSetSymbolClauses_nil_iff
    (sigma : Assignment)
    (varAt : Option Bool -> Nat)
    (target : Option Bool) :
    evalNTMCNF sigma (ntmSetSymbolClauses [] varAt target) = true <->
      forall a : Option Bool,
        sigma (varAt a) = decide (a = target) := by
  constructor
  · intro h a
    have hcl :
        evalNTMClause sigma
          [ntmLitFor (varAt a) (decide (a = target))] = true := by
      apply evalNTMCNF_of_mem sigma
        (ntmSetSymbolClauses [] varAt target)
        [ntmLitFor (varAt a) (decide (a = target))]
        h
      cases a with
      | none =>
          simp [ntmSetSymbolClauses, ntmAlphabet]
      | some av =>
          cases av <;>
            simp [ntmSetSymbolClauses, ntmAlphabet]
    exact (evalNTMClause_singleton_litFor
      sigma (varAt a) (decide (a = target))).mp hcl
  · intro h
    have hn :
        evalNTMClause sigma
          [ntmLitFor (varAt none) (decide (none = target))] = true :=
      (evalNTMClause_singleton_litFor
        sigma (varAt none) (decide (none = target))).2 (h none)
    have hf :
        evalNTMClause sigma
          [ntmLitFor (varAt (some false)) (decide (some false = target))] = true :=
      (evalNTMClause_singleton_litFor
        sigma (varAt (some false)) (decide (some false = target))).2 (h (some false))
    have ht :
        evalNTMClause sigma
          [ntmLitFor (varAt (some true)) (decide (some true = target))] = true :=
      (evalNTMClause_singleton_litFor
        sigma (varAt (some true)) (decide (some true = target))).2 (h (some true))
    simpa [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF] using
      And.intro hn (And.intro hf ht)

theorem eval_ntmSetLeftCell_nil_iff
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetLeftCell [] M x t 0 i a) = true <->
      forall b : Option Bool,
        sigma (ntmLeftVar M x t 0 i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmLeftVar M x t 0 i) a

theorem eval_ntmSetRightCell_nil_iff
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetRightCell [] M x t 0 i a) = true <->
      forall b : Option Bool,
        sigma (ntmRightVar M x t 0 i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmRightVar M x t 0 i) a

theorem eval_ntmSetLeftCell_nil_iff_at
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetLeftCell [] M x t s i a) = true <->
      forall b : Option Bool,
        sigma (ntmLeftVar M x t s i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmLeftVar M x t s i) a

theorem eval_ntmSetRightCell_nil_iff_at
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetRightCell [] M x t s i a) = true <->
      forall b : Option Bool,
        sigma (ntmRightVar M x t s i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmRightVar M x t s i) a

theorem evalNTMCNF_flatMap_range
    (sigma : Assignment) (n : Nat) (f : Nat -> NTMCNF) :
    evalNTMCNF sigma ((List.range n).flatMap f) = true <->
      forall i : Nat, i < n -> evalNTMCNF sigma (f i) = true := by
  induction n with
  | zero =>
      simp [evalNTMCNF]
  | succ n ih =>
      rw [List.range_succ]
      rw [List.flatMap_append]
      rw [evalNTMCNF_append]
      rw [ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hEq : i = n
        · subst i
          simpa using hlast
        · exact hprev i (by omega)
      · intro h
        constructor
        · intro i hi
          exact h i (by omega)
        · simpa using h n (by omega)

theorem evalNTMCNF_flatMap_list
    {α : Type}
    (sigma : Assignment)
    (xs : List α)
    (f : α -> NTMCNF) :
    evalNTMCNF sigma (xs.flatMap f) = true <->
      forall a, a ∈ xs -> evalNTMCNF sigma (f a) = true := by
  induction xs with
  | nil =>
      simp [evalNTMCNF]
  | cons a as ih =>
      rw [List.flatMap_cons]
      rw [evalNTMCNF_append]
      rw [ih]
      constructor
      · rintro ⟨ha, has⟩ x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact has x hx
      · intro h
        constructor
        · exact h a (by simp)
        · intro x hx
          exact h x (by simp [hx])

theorem evalNTMCNF_flatten
    (sigma : Assignment)
    (xss : List NTMCNF) :
    evalNTMCNF sigma xss.flatten = true <->
      forall xs, xs ∈ xss -> evalNTMCNF sigma xs = true := by
  simpa [List.flatten] using
    (evalNTMCNF_flatMap_list sigma xss (fun xs => xs))

theorem evalNTMCNF_map_flatten_ofFn
    {n : Nat}
    (sigma : Assignment)
    (f : Fin n -> NTMCNF) :
    evalNTMCNF sigma (List.ofFn f).flatten = true <->
      forall i : Fin n, evalNTMCNF sigma (f i) = true := by
  rw [evalNTMCNF_flatten]
  constructor
  · intro h i
    exact h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨i, rfl⟩
    exact h i

theorem evalNTMClause_append
    (sigma : Assignment) (c1 c2 : NTMClause) :
    evalNTMClause sigma (c1 ++ c2) = true <->
      evalNTMClause sigma c1 = true \/
      evalNTMClause sigma c2 = true := by
  induction c1 with
  | nil =>
      simp [evalNTMClause]
  | cons l ls ih =>
      simp [evalNTMClause, ih, Bool.or_eq_true, or_assoc]

theorem evalNTMClause_map_pos_exists
    {α : Type}
    (sigma : Assignment)
    (xs : List α)
    (v : α -> Nat) :
    evalNTMClause sigma (xs.map (fun a => ntmPos (v a))) = true <->
      ∃ a ∈ xs, sigma (v a) = true := by
  induction xs with
  | nil =>
      simp [evalNTMClause]
  | cons a as ih =>
      change
        (sigma (v a) || evalNTMClause sigma (as.map (fun x => ntmPos (v x)))) = true <->
          ∃ x, x ∈ a :: as ∧ sigma (v x) = true
      rw [Bool.or_eq_true]
      constructor
      · intro h
        rcases h with ha | ht
        · exact ⟨a, by simp, ha⟩
        · have hex : ∃ x ∈ as, sigma (v x) = true := ih.mp ht
          rcases hex with ⟨x, hx, hv⟩
          exact ⟨x, by simp [hx], hv⟩
      · rintro ⟨x, hx, hv⟩
        simp only [List.mem_cons] at hx
        rcases hx with hxa | hx
        · subst x
          exact Or.inl hv
        · exact Or.inr (ih.mpr ⟨x, hx, hv⟩)

theorem indexedTransitionsAux_index_lt
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (start j : Nat) (tr : State × Symbol × Direction)
    (h : (j, tr) ∈ ntmIndexedTransitionsAux start ts) :
    j < start + ts.length := by
  induction ts generalizing start j tr with
  | nil =>
      simp [ntmIndexedTransitionsAux] at h
  | cons x xs ih =>
      simp only [ntmIndexedTransitionsAux, List.mem_cons] at h
      rcases h with hhead | htail
      · cases hhead
        simp
      · have hlt := ih (start + 1) j tr htail
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

theorem indexedTransitions_index_lt
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    {j : Nat} {tr : State × Symbol × Direction}
    (h : (j, tr) ∈ ntmIndexedTransitions ts) :
    j < ts.length := by
  unfold ntmIndexedTransitions at h
  have hlt := indexedTransitionsAux_index_lt ts 0 j tr h
  simpa using hlt

theorem indexedTransitionsAux_index_ge
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (start j : Nat) (tr : State × Symbol × Direction)
    (hmem : (j, tr) ∈ ntmIndexedTransitionsAux start ts) :
    start ≤ j := by
  induction ts generalizing start j tr with
  | nil =>
      simp [ntmIndexedTransitionsAux] at hmem
  | cons x xs ih =>
      simp only [ntmIndexedTransitionsAux, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        exact Nat.le_refl start
      · have hge := ih (start + 1) j tr htail
        omega

theorem indexedTransitionsAux_index_value
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (start j : Nat) (tr : State × Symbol × Direction)
    (hmem : (start + j, tr) ∈ ntmIndexedTransitionsAux start ts)
    (hj : j < ts.length) :
    tr = ts.get ⟨j, hj⟩ := by
  induction ts generalizing start j tr with
  | nil =>
      simp at hj
  | cons x xs ih =>
      cases j with
      | zero =>
          simp only [Nat.add_zero, ntmIndexedTransitionsAux, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            rfl
          · have hge :=
              indexedTransitionsAux_index_ge xs (start + 1) start tr htail
            omega
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          simp only [ntmIndexedTransitionsAux, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · have hEq : start + (j + 1) = start := congrArg Prod.fst hhead
            omega
          · have htail' :
                ((start + 1) + j, tr) ∈
                  ntmIndexedTransitionsAux (start + 1) xs := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
            have hval := ih (start + 1) j tr htail' hj'
            simpa using hval

theorem indexedTransitions_index_value
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat) (tr : State × Symbol × Direction)
    (hmem : (j, tr) ∈ ntmIndexedTransitions ts)
    (hj : j < ts.length) :
    tr = ts.get ⟨j, hj⟩ := by
  unfold ntmIndexedTransitions at hmem
  have h :=
    indexedTransitionsAux_index_value ts 0 j tr
      (by simpa using hmem) hj
  simpa using h

theorem boundedExec_transitionStep_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t) :
    evalNTMCNF sigma (ntmTransitionStepCNF M x t s) = true := by
  have hAll :=
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)).mp
      (by simpa [boundedExecTableauCNF_NTM, List.append_assoc] using hSat)
  have hTransFinal := hAll.2
  have hTrans :=
    (evalNTMCNF_append sigma
      (ntmTransitionsCNF M x t)
      (ntmFinalAcceptanceCNF M t)).mp hTransFinal
  exact (evalNTMCNF_flatMap_range sigma t
    (fun r => ntmTransitionStepCNF M x t r)).mp
      (by simpa [ntmTransitionsCNF] using hTrans.1) s hs

theorem transitionStep_case_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hStep : evalNTMCNF sigma (ntmTransitionStepCNF M x t s) = true) :
    evalNTMCNF sigma (ntmTransitionCaseCNF M x t s q a) = true := by
  have hq :=
    (evalNTMCNF_map_flatten_ofFn sigma
      (fun q : Fin (M.stateCount + 1) =>
        ntmAlphabet.flatMap fun a =>
          ntmTransitionCaseCNF M x t s q a)).mp
      (by simpa [ntmTransitionStepCNF] using hStep) q
  exact (evalNTMCNF_flatMap_list sigma ntmAlphabet
    (fun a => ntmTransitionCaseCNF M x t s q a)).mp hq a
      (by cases a <;> simp [ntmAlphabet])

theorem activeChoice_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hCase : evalNTMCNF sigma (ntmTransitionCaseCNF M x t s q a) = true)
    (hActive :
      M.machine.accepting q = false ∧
      M.machine.rejecting q = false) :
    evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true := by
  cases ha : M.machine.accepting q <;>
    cases hr : M.machine.rejecting q <;>
    simp_all [ntmTransitionCaseCNF]

theorem ntmChoice_exists_nat_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true) :
    ∃ j tr,
      (j, tr) ∈ ntmIndexedTransitions (M.machine.transition q a) ∧
      sigma (ntmChoiceVar M x t s q a j) = true := by
  have hfirst :=
    (evalNTMCNF_append sigma
      [ntmGuardChoiceClause M x t s q a]
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
          (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
       ntmAtMostOneChoiceCNF M x t s q a ++
       (ntmIndexedTransitions (M.machine.transition q a)).flatMap
          (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      (by simpa [ntmActiveChoiceCNF, List.append_assoc] using hActiveSat)
  have hclause :
      evalNTMClause sigma (ntmGuardChoiceClause M x t s q a) = true := by
    simpa [evalNTMCNF] using hfirst.1
  have htail :
      evalNTMClause sigma
        ((ntmIndexedTransitions (M.machine.transition q a)).map
          (fun p => ntmPos (ntmChoiceVar M x t s q a p.1))) = true := by
    have happ :=
      (evalNTMClause_append sigma
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        ((ntmIndexedTransitions (M.machine.transition q a)).map
          (fun p => ntmPos (ntmChoiceVar M x t s q a p.1)))).mp
        (by simpa [ntmGuardChoiceClause] using hclause)
    rcases happ with hneg | htail
    · simp [evalNTMClause, evalNTMLiteral, ntmNeg, hq, ha] at hneg
    · exact htail
  rcases (evalNTMClause_map_pos_exists sigma
    (ntmIndexedTransitions (M.machine.transition q a))
    (fun p => ntmChoiceVar M x t s q a p.1)).mp htail with
    ⟨p, hp, hptrue⟩
  exact ⟨p.1, p.2, hp, hptrue⟩

theorem ntmChoice_exists_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    ∃ j : Fin (M.machine.transition q a).length,
      sigma (ntmChoiceVar M x t s q a j.val) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  rcases ntmChoice_exists_nat_of_guard
      M x t s q a sigma hActiveSat hq ha with
    ⟨j, tr, hjmem, hjtrue⟩
  exact ⟨⟨j, indexedTransitions_index_lt
    (M.machine.transition q a) hjmem⟩, hjtrue⟩

theorem boundedExecCircuit_NTM_isCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    IsCNF (boundedExecCircuit_NTM M x t) := by
  exact ntmCNFCircuit_isCNF _


theorem indexedTransitionsAux_index_mem
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (start j : Nat)
    (hj : j < ts.length) :
    (start + j, ts.get ⟨j, hj⟩) ∈ ntmIndexedTransitionsAux start ts := by
  induction ts generalizing start j with
  | nil =>
      simp at hj
  | cons x xs ih =>
      cases j with
      | zero =>
          simp [ntmIndexedTransitionsAux]
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          simp only [ntmIndexedTransitionsAux, List.mem_cons]
          right
          have hmem := ih (start + 1) j hj'
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem indexedTransitions_index_mem
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat)
    (hj : j < ts.length) :
    ∃ tr, (j, tr) ∈ ntmIndexedTransitions ts := by
  refine ⟨ts.get ⟨j, hj⟩, ?_⟩
  unfold ntmIndexedTransitions
  simpa using indexedTransitionsAux_index_mem ts 0 j hj

theorem indexedTransitions_index_in_ids
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat)
    (hj : j < ts.length) :
    j ∈ (ntmIndexedTransitions ts).map Prod.fst := by
  rcases indexedTransitions_index_mem ts j hj with ⟨tr, hmem⟩
  exact List.mem_map.mpr ⟨(j, tr), hmem, rfl⟩

theorem activeChoice_atMostOne_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have hcanon :
      evalNTMCNF sigma
        ([ntmGuardChoiceClause M x t s q a] ++
         entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
    simpa [ntmActiveChoiceCNF, entries] using hActiveSat
  have hA :=
      (evalNTMCNF_append sigma
        [ntmGuardChoiceClause M x t s q a]
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hcanon
  have hA2 :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         (ntmAtMostOneChoiceCNF M x t s q a ++
          entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))) = true := by
    simpa [List.append_assoc] using hA.2
  have hB :=
      (evalNTMCNF_append sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
        (ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hA2
  have hC :=
      (evalNTMCNF_append sigma
        (ntmAtMostOneChoiceCNF M x t s q a)
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hB.2
  have hparts :
      evalNTMCNF sigma [ntmGuardChoiceClause M x t s q a] = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true ∧
      evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true :=
    ⟨hA.1, hB.1, hC.1, hC.2⟩
  exact hparts.2.2.1

theorem activeChoice_choiceGuards_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have hcanon :
      evalNTMCNF sigma
        ([ntmGuardChoiceClause M x t s q a] ++
         entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
    simpa [ntmActiveChoiceCNF, entries] using hActiveSat
  have hA :=
      (evalNTMCNF_append sigma
        [ntmGuardChoiceClause M x t s q a]
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hcanon
  have hA2 :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         (ntmAtMostOneChoiceCNF M x t s q a ++
          entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))) = true := by
    simpa [List.append_assoc] using hA.2
  have hB :=
      (evalNTMCNF_append sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
        (ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hA2
  have hC :=
      (evalNTMCNF_append sigma
        (ntmAtMostOneChoiceCNF M x t s q a)
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hB.2
  have hparts :
      evalNTMCNF sigma [ntmGuardChoiceClause M x t s q a] = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true ∧
      evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true :=
    ⟨hA.1, hB.1, hC.1, hC.2⟩
  simpa [entries] using hparts.2.1

theorem ntmAtMostOne_pair_mem
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j k : Nat)
    (hj : j < (M.machine.transition q a).length)
    (hk : k < (M.machine.transition q a).length)
    (hjk : j < k) :
    [ntmNeg (ntmChoiceVar M x t s q a j),
     ntmNeg (ntmChoiceVar M x t s q a k)] ∈
      ntmAtMostOneChoiceCNF M x t s q a := by
  let ids := (ntmIndexedTransitions (M.machine.transition q a)).map Prod.fst
  have hjmem : j ∈ ids := by
    simpa [ids] using
      indexedTransitions_index_in_ids (M.machine.transition q a) j hj
  have hkmem : k ∈ ids := by
    simpa [ids] using
      indexedTransitions_index_in_ids (M.machine.transition q a) k hk
  unfold ntmAtMostOneChoiceCNF
  simp only [List.mem_flatMap]
  refine ⟨j, hjmem, ?_⟩
  refine ⟨k, hkmem, ?_⟩
  simp [hjk]

theorem ntmChoice_unique_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (j1 j2 : Fin (M.machine.transition q a).length)
    (h1 : sigma (ntmChoiceVar M x t s q a j1.val) = true)
    (h2 : sigma (ntmChoiceVar M x t s q a j2.val) = true) :
    j1 = j2 := by
  by_cases hEq : j1 = j2
  · exact hEq
  · have hneVal : j1.val ≠ j2.val := by
      intro hval
      apply hEq
      exact Fin.ext hval
    have hlt : j1.val < j2.val ∨ j2.val < j1.val := by
      omega
    have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
    have hCase := transitionStep_case_sat M x t s q a sigma hStep
    have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
    have hAtMost := activeChoice_atMostOne_sat M x t s q a sigma hActiveSat
    exfalso
    rcases hlt with h12 | h21
    · have hmem := ntmAtMostOne_pair_mem M x t s q a
          j1.val j2.val j1.isLt j2.isLt h12
      have hc := evalNTMCNF_of_mem sigma
        (ntmAtMostOneChoiceCNF M x t s q a) _ hAtMost hmem
      simpa [evalNTMClause, evalNTMLiteral, ntmNeg, h1, h2] using hc
    · have hmem := ntmAtMostOne_pair_mem M x t s q a
          j2.val j1.val j2.isLt j1.isLt h21
      have hc := evalNTMCNF_of_mem sigma
        (ntmAtMostOneChoiceCNF M x t s q a) _ hAtMost hmem
      simpa [evalNTMClause, evalNTMLiteral, ntmNeg, h1, h2] using hc

theorem ntmChoice_exists_unique_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    ∃ j : Fin (M.machine.transition q a).length,
      sigma (ntmChoiceVar M x t s q a j.val) = true ∧
      ∀ k : Fin (M.machine.transition q a).length,
        sigma (ntmChoiceVar M x t s q a k.val) = true → k = j := by
  rcases ntmChoice_exists_of_guard M x t s q a sigma
      hSat hs hq ha hActive with ⟨j, hj⟩
  refine ⟨j, hj, ?_⟩
  intro k hk
  exact ntmChoice_unique_of_guard M x t s q a sigma
    hSat hs hActive k j hk hj

theorem ntmChoice_implies_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmStateVar M t s q) = true ∧
      sigma (ntmHeadVar M t s a) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hGuards := activeChoice_choiceGuards_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j hjLt with ⟨tr, hmem⟩
  have hblock :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceGuardCNF M x t s q a p.1)).mp
      hGuards (j, tr) hmem
  have hfirst :
      evalNTMClause sigma
        [ntmNeg (ntmChoiceVar M x t s q a j),
         ntmPos (ntmStateVar M t s q)] = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmChoiceGuardCNF M x t s q a j) _
      hblock
    simp [ntmChoiceGuardCNF]
  have hsecond :
      evalNTMClause sigma
        [ntmNeg (ntmChoiceVar M x t s q a j),
         ntmPos (ntmHeadVar M t s a)] = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmChoiceGuardCNF M x t s q a j) _
      hblock
    simp [ntmChoiceGuardCNF]
  constructor
  · cases hsq : sigma (ntmStateVar M t s q) <;>
      simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos, hj, hsq] at hfirst ⊢
  · cases hha : sigma (ntmHeadVar M t s a) <;>
      simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos, hj, hha] at hsecond ⊢

theorem ntmChoice_implies_state
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmStateVar M t s q) = true :=
  (ntmChoice_implies_guard M x t s q a j hjLt sigma hSat hs hActive hj).1

theorem ntmChoice_implies_head
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmHeadVar M t s a) = true :=
  (ntmChoice_implies_guard M x t s q a j hjLt sigma hSat hs hActive hj).2



theorem activeChoice_choiceEffects_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have hcanon :
      evalNTMCNF sigma
        ([ntmGuardChoiceClause M x t s q a] ++
         entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
    simpa [ntmActiveChoiceCNF, entries] using hActiveSat
  have hA :=
      (evalNTMCNF_append sigma
        [ntmGuardChoiceClause M x t s q a]
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hcanon
  have hA2 :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
         (ntmAtMostOneChoiceCNF M x t s q a ++
          entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))) = true := by
    simpa [List.append_assoc] using hA.2
  have hB :=
      (evalNTMCNF_append sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
        (ntmAtMostOneChoiceCNF M x t s q a ++
         entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hA2
  have hC :=
      (evalNTMCNF_append sigma
        (ntmAtMostOneChoiceCNF M x t s q a)
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp hB.2
  have hparts :
      evalNTMCNF sigma [ntmGuardChoiceClause M x t s q a] = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true ∧
      evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true ∧
      evalNTMCNF sigma (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true :=
    ⟨hA.1, hB.1, hC.1, hC.2⟩
  simpa [entries] using hparts.2.2.2

theorem choiceEffect_block_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    ∃ tr,
      (j, tr) ∈ ntmIndexedTransitions (M.machine.transition q a) ∧
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a (j, tr)) = true := by
  have hEffects :=
    activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j hjLt with ⟨tr, hmem⟩
  refine ⟨tr, hmem, ?_⟩
  exact (evalNTMCNF_flatMap_list sigma
    (ntmIndexedTransitions (M.machine.transition q a))
    (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
    hEffects (j, tr) hmem

theorem evalNTMClause_neg_prefix_true
    (sigma : Assignment) (cvar : Nat) (cl : NTMClause)
    (h : evalNTMClause sigma (ntmNeg cvar :: cl) = true)
    (hc : sigma cvar = true) :
    evalNTMClause sigma cl = true := by
  simpa [evalNTMClause, evalNTMLiteral, ntmNeg, hc] using h

theorem eval_setState_neg_guard_to_nil
    (M : PolyNTMCandidate)
    (t s : Nat)
    (cvar : Nat)
    (target : Fin (M.stateCount + 1))
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetStateClauses [ntmNeg cvar] M t s target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetStateClauses [] M t s target) = true := by
  rw [eval_ntmSetStateClauses_nil_iff]
  intro r
  have hguarded :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmLitFor (ntmStateVar M t s r) (decide (r = target))]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmSetStateClauses [ntmNeg cvar] M t s target) _
      h
    rw [show ntmSetStateClauses [ntmNeg cvar] M t s target =
      List.ofFn (fun q : Fin (M.stateCount + 1) =>
        [ntmNeg cvar] ++
          [ntmLitFor (ntmStateVar M t s q) (decide (q = target))]) by rfl]
    exact List.mem_ofFn.mpr ⟨r, rfl⟩
  have hunit :
      evalNTMClause sigma
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))] = true := by
    exact evalNTMClause_neg_prefix_true sigma cvar _ (by simpa using hguarded) hc
  exact (evalNTMClause_singleton_litFor
    sigma (ntmStateVar M t s r) (decide (r = target))).mp hunit

theorem eval_setSymbol_neg_guard_to_nil
    (varAt : Option Bool -> Nat)
    (cvar : Nat)
    (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetSymbolClauses [ntmNeg cvar] varAt target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetSymbolClauses [] varAt target) = true := by
  rw [eval_ntmSetSymbolClauses_nil_iff]
  intro b
  have hguarded :
      evalNTMClause sigma
        ([ntmNeg cvar] ++ [ntmLitFor (varAt b) (decide (b = target))]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmSetSymbolClauses [ntmNeg cvar] varAt target) _
      h
    cases b with
    | none =>
        simp [ntmSetSymbolClauses, ntmAlphabet]
    | some bv =>
        cases bv <;>
          simp [ntmSetSymbolClauses, ntmAlphabet]
  have hunit :
      evalNTMClause sigma [ntmLitFor (varAt b) (decide (b = target))] = true := by
    exact evalNTMClause_neg_prefix_true sigma cvar _ (by simpa using hguarded) hc
  exact (evalNTMClause_singleton_litFor sigma (varAt b) (decide (b = target))).mp hunit

theorem eval_copySymbol_neg_guard_of_choice_true
    (sigma : Assignment)
    (cvar : Nat)
    (oldVar newVar : Option Bool -> Nat)
    (h :
      evalNTMCNF sigma
        (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) = true)
    (hc : sigma cvar = true) :
    forall a : Option Bool,
      sigma (newVar a) = sigma (oldVar a) := by
  intro a
  have hforward :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmNeg (oldVar a), ntmPos (newVar a)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) _
      h
    cases a with
    | none =>
        simp [ntmCopySymbolClauses, ntmAlphabet]
    | some av =>
        cases av <;>
          simp [ntmCopySymbolClauses, ntmAlphabet]
  have hbackward :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmPos (oldVar a), ntmNeg (newVar a)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) _
      h
    cases a with
    | none =>
        simp [ntmCopySymbolClauses, ntmAlphabet]
    | some av =>
        cases av <;>
          simp [ntmCopySymbolClauses, ntmAlphabet]
  have hf :
      evalNTMClause sigma
        [ntmNeg (oldVar a), ntmPos (newVar a)] = true :=
    evalNTMClause_neg_prefix_true sigma cvar _
      (by simpa using hforward) hc
  have hb :
      evalNTMClause sigma
        [ntmPos (oldVar a), ntmNeg (newVar a)] = true :=
    evalNTMClause_neg_prefix_true sigma cvar _
      (by simpa using hbackward) hc
  cases hold : sigma (oldVar a) <;>
    cases hnew : sigma (newVar a) <;>
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos,
      hold, hnew] at hf hb ⊢

theorem choiceEffect_stateBlock_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true) :
    evalNTMCNF sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M t (s + 1) entry.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  cases d <;>
    simp [ntmChoiceEffectCNF, ntmStayEffectCNF,
      ntmLeftEffectCNF, ntmRightEffectCNF,
      evalNTMCNF_append, List.append_assoc] at hEff ⊢
  · exact hEff.1
  · exact hEff.1
  · exact hEff.1

theorem ntmChoice_effect_state_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ r : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t (s + 1) r) =
        decide (r = ((M.machine.transition q a).get j).1) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      exact indexedTransitions_index_value
        (M.machine.transition q a) j.val tr hmem j.isLt
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hStateGuarded :=
    choiceEffect_stateBlock_sat M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff
  have hStateNil :=
    eval_setState_neg_guard_to_nil
      M t (s + 1)
      (ntmChoiceVar M x t s q a j.val)
      ((M.machine.transition q a).get j).1
      sigma hStateGuarded hj
  exact (eval_ntmSetStateClauses_nil_iff
    sigma M t (s + 1)
    ((M.machine.transition q a).get j).1).mp hStateNil




theorem choiceEffect_headBlock_sat_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.stay) :
    evalNTMCNF sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmHeadVar M t (s + 1)) entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmSetSymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmHeadVar M t (s + 1)) write)
    (ntmCopyLeftAll
      [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s ++
     ntmCopyRightAll
      [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s)).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem choiceEffect_headCopy_sat_left
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmLeftVar M x t s 0)
        (ntmHeadVar M t (s + 1))) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0)
        (ntmHeadVar M t (s + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyLeftCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (i + 1) (s + 1) i) ++
       ntmSetLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyRightCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s i (s + 1) (i + 1)))).mp
      (by simpa [ntmChoiceEffectCNF, ntmLeftEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmCopySymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmLeftVar M x t s 0)
      (ntmHeadVar M t (s + 1)))
    ((List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s (i + 1) (s + 1) i) ++
     ntmSetLeftCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
     ntmSetRightCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) 0 write ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s i (s + 1) (i + 1)))).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem choiceEffect_headCopy_sat_right
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmRightVar M x t s 0)
        (ntmHeadVar M t (s + 1))) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmRightVar M x t s 0)
        (ntmHeadVar M t (s + 1)) ++
       ntmSetLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyLeftCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s i (s + 1) (i + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyRightCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (i + 1) (s + 1) i) ++
       ntmSetRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank)).mp
      (by simpa [ntmChoiceEffectCNF, ntmRightEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmCopySymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmRightVar M x t s 0)
      (ntmHeadVar M t (s + 1)))
    (ntmSetLeftCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) 0 write ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
       ntmCopyLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t s i (s + 1) (i + 1)) ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
       ntmCopyRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t s (i + 1) (s + 1) i) ++
     ntmSetRightCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) (ntmRadius x t - 1) M.machine.blank)).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem ntmChoice_effect_head_exact_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        decide (b = ((M.machine.transition q a).get j).2.1) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    exact indexedTransitions_index_value
      (M.machine.transition q a) j.val tr hmem j.isLt
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hHeadGuarded :=
    choiceEffect_headBlock_sat_stay M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hHeadNil :=
    eval_setSymbol_neg_guard_to_nil
      (ntmHeadVar M t (s + 1))
      (ntmChoiceVar M x t s q a j.val)
      ((M.machine.transition q a).get j).2.1
      sigma hHeadGuarded hj
  exact (eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmHeadVar M t (s + 1))
    ((M.machine.transition q a).get j).2.1).mp hHeadNil

theorem ntmChoice_effect_head_exact_left
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        sigma (ntmLeftVar M x t s 0 b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    exact indexedTransitions_index_value
      (M.machine.transition q a) j.val tr hmem j.isLt
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    choiceEffect_headCopy_sat_left M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s 0)
    (ntmHeadVar M t (s + 1))
    hCopy hj

theorem ntmChoice_effect_head_exact_right
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        sigma (ntmRightVar M x t s 0 b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    exact indexedTransitions_index_value
      (M.machine.transition q a) j.val tr hmem j.isLt
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    choiceEffect_headCopy_sat_right M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s 0)
    (ntmHeadVar M t (s + 1))
    hCopy hj

theorem stay_copyLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry :
      Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hStay : entry.2.2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmLeftVar M x t s i)
        (ntmLeftVar M x t (s + 1) i)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hStay
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write)
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)
      (ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp h2.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun r =>
      ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s r)
        (ntmLeftVar M x t (s + 1) r))).mp
      (by simpa [ntmCopyLeftAll] using h3.1) i hi

theorem stay_copyRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry :
      Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hStay : entry.2.2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmRightVar M x t s i)
        (ntmRightVar M x t (s + 1) i)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hStay
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write)
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)
      (ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp h2.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun r =>
      ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmRightVar M x t s r)
        (ntmRightVar M x t (s + 1) r))).mp
      (by simpa [ntmCopyRightAll] using h3.2) i hi

theorem ntmStay_left_copy_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hStay :
      ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) i b) =
        sigma (ntmLeftVar M x t s i b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      exact indexedTransitions_index_value
        (M.machine.transition q a) j.val tr hmem j.isLt
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    stay_copyLeft_sat M x t s q a
      (j.val, (M.machine.transition q a).get j)
      sigma hEff hStay i hi
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s i)
    (ntmLeftVar M x t (s + 1) i)
    hCopy hj

theorem ntmStay_right_copy_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hStay :
      ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) i b) =
        sigma (ntmRightVar M x t s i b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      exact indexedTransitions_index_value
        (M.machine.transition q a) j.val tr hmem j.isLt
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    stay_copyRight_sat M x t s q a
      (j.val, (M.machine.transition q a).get j)
      sigma hEff hStay i hi
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s i)
    (ntmRightVar M x t (s + 1) i)
    hCopy hj



theorem eval_setLeft_neg_guard_to_nil
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (cvar : Nat) (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetLeftCell [ntmNeg cvar] M x t s i target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetLeftCell [] M x t s i target) = true := by
  exact eval_setSymbol_neg_guard_to_nil
    (ntmLeftVar M x t s i) cvar target sigma h hc

theorem eval_setRight_neg_guard_to_nil
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (cvar : Nat) (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetRightCell [ntmNeg cvar] M x t s i target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetRightCell [] M x t s i target) = true := by
  exact eval_setSymbol_neg_guard_to_nil
    (ntmRightVar M x t s i) cvar target sigma h hc

theorem leftEffect_shiftedLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s (i + 1) (s + 1) i) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s (k + 1) (s + 1) k)).mp hEff.2.2.1 i hi

theorem leftEffect_blankLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.2.1

theorem leftEffect_writeRight0_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) 0 entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.2.2.1


theorem leftEffect_shiftedRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s i (s + 1) (i + 1)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s k (s + 1) (k + 1))).mp hEff.2.2.2.2.2 i hi

theorem rightEffect_writeLeft0_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) 0 entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.1

theorem rightEffect_shiftedLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s i (s + 1) (i + 1)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s k (s + 1) (k + 1))).mp hEff.2.2.2.1 i hi

theorem rightEffect_shiftedRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s (i + 1) (s + 1) i) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s (k + 1) (s + 1) k)).mp hEff.2.2.2.2.1 i hi

theorem rightEffect_blankRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.2.2.2



theorem selectedChoiceEffect_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    evalNTMCNF sigma
      (ntmChoiceEffectCNF M x t s q a
        (j.val, (M.machine.transition q a).get j)) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    exact indexedTransitions_index_value
      (M.machine.transition q a) j.val tr hmem j.isLt
  have hmem' :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  exact (evalNTMCNF_flatMap_list sigma
    (ntmIndexedTransitions (M.machine.transition q a))
    (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmem'

theorem ntmLeft_shiftedRight_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) (i + 1) b) =
        sigma (ntmRightVar M x t s i b) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hcopy := leftEffect_shiftedRight_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir i hi
  exact eval_copySymbol_neg_guard_of_choice_true sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s i)
    (ntmRightVar M x t (s + 1) (i + 1)) hcopy hj

theorem ntmRight_shiftedLeft_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) (i + 1) b) =
        sigma (ntmLeftVar M x t s i b) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hcopy := rightEffect_shiftedLeft_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir i hi
  exact eval_copySymbol_neg_guard_of_choice_true sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s i)
    (ntmLeftVar M x t (s + 1) (i + 1)) hcopy hj

theorem ntmRight_shiftedRight_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) i b) =
        sigma (ntmRightVar M x t s (i + 1) b) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hcopy := rightEffect_shiftedRight_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir i hi
  exact eval_copySymbol_neg_guard_of_choice_true sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s (i + 1))
    (ntmRightVar M x t (s + 1) i) hcopy hj

theorem ntmRight_writeLeft0_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) 0 b) =
        decide (b = ((M.machine.transition q a).get j).2.1) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hset := rightEffect_writeLeft0_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hnil := eval_setLeft_neg_guard_to_nil M x t (s + 1) 0
    (ntmChoiceVar M x t s q a j.val)
    ((M.machine.transition q a).get j).2.1 sigma hset hj
  exact (eval_ntmSetLeftCell_nil_iff_at M x t (s + 1) sigma 0
    ((M.machine.transition q a).get j).2.1).mp hnil

theorem ntmRight_blankRight_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) (ntmRadius x t - 1) b) =
        decide (b = M.machine.blank) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hset := rightEffect_blankRight_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hnil := eval_setRight_neg_guard_to_nil M x t (s + 1) (ntmRadius x t - 1)
    (ntmChoiceVar M x t s q a j.val) M.machine.blank sigma hset hj
  exact (eval_ntmSetRightCell_nil_iff_at M x t (s + 1) sigma (ntmRadius x t - 1)
    M.machine.blank).mp hnil


theorem haltedCase_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  rcases hHalt with ha | hr
  · simpa [ntmTransitionCaseCNF, ha] using hCase
  · simpa [ntmTransitionCaseCNF, hr] using hCase

theorem evalNTMClause_two_neg_prefix_true
    (sigma : Assignment) (c1 c2 : Nat) (cl : NTMClause)
    (h : evalNTMClause sigma (ntmNeg c1 :: ntmNeg c2 :: cl) = true)
    (hc1 : sigma c1 = true)
    (hc2 : sigma c2 = true) :
    evalNTMClause sigma cl = true := by
  simpa [evalNTMClause, evalNTMLiteral, ntmNeg, hc1, hc2] using h

theorem eval_setState_two_neg_guard_to_nil
    (M : PolyNTMCandidate) (t s : Nat)
    (c1 c2 : Nat)
    (target : Fin (M.stateCount + 1))
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetStateClauses [ntmNeg c1, ntmNeg c2] M t s target) = true)
    (hc1 : sigma c1 = true)
    (hc2 : sigma c2 = true) :
    evalNTMCNF sigma (ntmSetStateClauses [] M t s target) = true := by
  rw [eval_ntmSetStateClauses_nil_iff]
  intro r
  have hguarded :
      evalNTMClause sigma
        ([ntmNeg c1, ntmNeg c2] ++
          [ntmLitFor (ntmStateVar M t s r) (decide (r = target))]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmSetStateClauses [ntmNeg c1, ntmNeg c2] M t s target) _
      h
    rw [show ntmSetStateClauses [ntmNeg c1, ntmNeg c2] M t s target =
      List.ofFn (fun q : Fin (M.stateCount + 1) =>
        [ntmNeg c1, ntmNeg c2] ++
          [ntmLitFor (ntmStateVar M t s q) (decide (q = target))]) by rfl]
    exact List.mem_ofFn.mpr ⟨r, rfl⟩
  have hunit :
      evalNTMClause sigma
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))] = true := by
    exact evalNTMClause_two_neg_prefix_true sigma c1 c2 _
      (by simpa using hguarded) hc1 hc2
  exact (evalNTMClause_singleton_litFor
    sigma (ntmStateVar M t s r) (decide (r = target))).mp hunit

theorem eval_copySymbol_two_neg_guard_true
    (sigma : Assignment)
    (c1 c2 : Nat)
    (oldVar newVar : Option Bool -> Nat)
    (h :
      evalNTMCNF sigma
        (ntmCopySymbolClauses [ntmNeg c1, ntmNeg c2] oldVar newVar) = true)
    (hc1 : sigma c1 = true)
    (hc2 : sigma c2 = true) :
    forall b : Option Bool, sigma (newVar b) = sigma (oldVar b) := by
  intro b
  have hfwd :
      evalNTMClause sigma
        ([ntmNeg c1, ntmNeg c2] ++
          [ntmNeg (oldVar b), ntmPos (newVar b)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg c1, ntmNeg c2] oldVar newVar) _
      h
    cases b with
    | none =>
        simp [ntmCopySymbolClauses, ntmAlphabet]
    | some bv =>
        cases bv <;> simp [ntmCopySymbolClauses, ntmAlphabet]
  have hbwd :
      evalNTMClause sigma
        ([ntmNeg c1, ntmNeg c2] ++
          [ntmPos (oldVar b), ntmNeg (newVar b)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg c1, ntmNeg c2] oldVar newVar) _
      h
    cases b with
    | none =>
        simp [ntmCopySymbolClauses, ntmAlphabet]
    | some bv =>
        cases bv <;> simp [ntmCopySymbolClauses, ntmAlphabet]
  have hf :
      evalNTMClause sigma [ntmNeg (oldVar b), ntmPos (newVar b)] = true :=
    evalNTMClause_two_neg_prefix_true sigma c1 c2 _
      (by simpa using hfwd) hc1 hc2
  have hb :
      evalNTMClause sigma [ntmPos (oldVar b), ntmNeg (newVar b)] = true :=
    evalNTMClause_two_neg_prefix_true sigma c1 c2 _
      (by simpa using hbwd) hc1 hc2
  cases ho : sigma (oldVar b) <;>
    cases hn : sigma (newVar b) <;>
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos, ho, hn] at hf hb ⊢

theorem halted_stateBlock_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hHaltedSat : evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true) :
    evalNTMCNF sigma
      (ntmSetStateClauses
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        M t (s + 1) q) = true := by
  exact (evalNTMCNF_append sigma
    (ntmSetStateClauses
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M t (s + 1) q)
    (ntmCopyHeadCell
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M t s (s + 1) ++
     ntmCopyLeftAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s ++
     ntmCopyRightAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s)).mp
    (by simpa [ntmHaltedStutterCNF, List.append_assoc] using hHaltedSat) |>.1

theorem ntmHalted_state_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    forall r : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t (s + 1) r) = decide (r = q) := by
  have hh := haltedCase_sat M x t s q a sigma hSat hs hHalt
  have hb := halted_stateBlock_sat M x t s q a sigma hh
  have hnil := eval_setState_two_neg_guard_to_nil M t (s + 1)
    (ntmStateVar M t s q) (ntmHeadVar M t s a) q sigma hb hq ha
  exact (eval_ntmSetStateClauses_nil_iff sigma M t (s + 1) q).mp hnil

theorem halted_headBlock_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hHaltedSat : evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true) :
    evalNTMCNF sigma
      (ntmCopyHeadCell
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        M t s (s + 1)) = true := by
  have h1 := (evalNTMCNF_append sigma
    (ntmSetStateClauses
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M t (s + 1) q)
    (ntmCopyHeadCell
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M t s (s + 1) ++
     ntmCopyLeftAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s ++
     ntmCopyRightAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s)).mp
    (by simpa [ntmHaltedStutterCNF, List.append_assoc] using hHaltedSat)
  exact (evalNTMCNF_append sigma
    (ntmCopyHeadCell
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M t s (s + 1))
    (ntmCopyLeftAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s ++
     ntmCopyRightAll
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      M x t s)).mp h1.2 |>.1

theorem ntmHalted_head_copy
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    forall b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        sigma (ntmHeadVar M t s b) := by
  have hh := haltedCase_sat M x t s q a sigma hSat hs hHalt
  have hb := halted_headBlock_sat M x t s q a sigma hh
  exact eval_copySymbol_two_neg_guard_true sigma
    (ntmStateVar M t s q) (ntmHeadVar M t s a)
    (ntmHeadVar M t s) (ntmHeadVar M t (s + 1))
    (by simpa [ntmCopyHeadCell] using hb) hq ha

theorem halted_leftAll_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hHaltedSat : evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true) :
    evalNTMCNF sigma
      (ntmCopyLeftAll
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        M x t s) = true := by
  simp [ntmHaltedStutterCNF, evalNTMCNF_append, List.append_assoc] at hHaltedSat
  exact hHaltedSat.2.2.1

theorem halted_rightAll_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hHaltedSat : evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true) :
    evalNTMCNF sigma
      (ntmCopyRightAll
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        M x t s) = true := by
  simp [ntmHaltedStutterCNF, evalNTMCNF_append, List.append_assoc] at hHaltedSat
  exact hHaltedSat.2.2.2

theorem ntmHalted_left_copy
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) i b) =
        sigma (ntmLeftVar M x t s i b) := by
  have hh := haltedCase_sat M x t s q a sigma hSat hs hHalt
  have hall := halted_leftAll_sat M x t s q a sigma hh
  have hiSat := (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun k => ntmCopySymbolClauses
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      (ntmLeftVar M x t s k)
      (ntmLeftVar M x t (s + 1) k))).mp
    (by simpa [ntmCopyLeftAll] using hall) i hi
  exact eval_copySymbol_two_neg_guard_true sigma
    (ntmStateVar M t s q) (ntmHeadVar M t s a)
    (ntmLeftVar M x t s i) (ntmLeftVar M x t (s + 1) i)
    hiSat hq ha

theorem ntmHalted_right_copy
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) i b) =
        sigma (ntmRightVar M x t s i b) := by
  have hh := haltedCase_sat M x t s q a sigma hSat hs hHalt
  have hall := halted_rightAll_sat M x t s q a sigma hh
  have hiSat := (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun k => ntmCopySymbolClauses
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
      (ntmRightVar M x t s k)
      (ntmRightVar M x t (s + 1) k))).mp
    (by simpa [ntmCopyRightAll] using hall) i hi
  exact eval_copySymbol_two_neg_guard_true sigma
    (ntmStateVar M t s q) (ntmHeadVar M t s a)
    (ntmRightVar M x t s i) (ntmRightVar M x t (s + 1) i)
    hiSat hq ha


theorem ntmLeft_shiftedLeft_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) i b) =
        sigma (ntmLeftVar M x t s (i + 1) b) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hcopy := leftEffect_shiftedLeft_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir i hi
  exact eval_copySymbol_neg_guard_of_choice_true sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s (i + 1))
    (ntmLeftVar M x t (s + 1) i) hcopy hj

theorem ntmLeft_blankLeft_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) (ntmRadius x t - 1) b) =
        decide (b = M.machine.blank) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hset := leftEffect_blankLeft_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hnil := eval_setLeft_neg_guard_to_nil M x t (s + 1) (ntmRadius x t - 1)
    (ntmChoiceVar M x t s q a j.val) M.machine.blank sigma hset hj
  exact (eval_ntmSetLeftCell_nil_iff M x t sigma (ntmRadius x t - 1)
    M.machine.blank).mp hnil

theorem ntmLeft_writeRight0_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) 0 b) =
        decide (b = ((M.machine.transition q a).get j).2.1) := by
  have hEff := selectedChoiceEffect_sat M x t s q a j sigma hSat hs hActive
  have hset := leftEffect_writeRight0_sat M x t s q a
    (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hnil := eval_setRight_neg_guard_to_nil M x t (s + 1) 0
    (ntmChoiceVar M x t s q a j.val)
    ((M.machine.transition q a).get j).2.1 sigma hset hj
  exact (eval_ntmSetRightCell_nil_iff M x t sigma 0
    ((M.machine.transition q a).get j).2.1).mp hnil


structure NTMUniqueAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) : Prop where
  hState :
    ExistsUnique (fun q : Fin (M.stateCount + 1) =>
      sigma (ntmStateVar M t s q) = true)
  hHead :
    ExistsUnique (fun a : Option Bool =>
      sigma (ntmHeadVar M t s a) = true)
  hLeft :
    forall i : Nat, i < ntmRadius x t ->
      ExistsUnique (fun b : Option Bool =>
        sigma (ntmLeftVar M x t s i b) = true)
  hRight :
    forall i : Nat, i < ntmRadius x t ->
      ExistsUnique (fun b : Option Bool =>
        sigma (ntmRightVar M x t s i b) = true)

theorem existsUnique_of_exact_decide
    {α : Type}
    [DecidableEq α]
    (f : α -> Bool)
    (target : α)
    (h : forall a : α, f a = decide (a = target)) :
    ∃! a : α, f a = true := by
  refine ⟨target, ?_, ?_⟩
  · simpa using h target
  · intro a ha
    have hd : decide (a = target) = true := by
      simpa [ha] using (h a).symm
    exact of_decide_eq_true hd

theorem existsUnique_transport
    {α : Type}
    (old new : α -> Bool)
    (hOld : ∃! a : α, old a = true)
    (hEq : forall a : α, new a = old a) :
    ∃! a : α, new a = true := by
  rcases hOld with ⟨a, ha, huniq⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [hEq a] using ha
  · intro b hb
    apply huniq b
    simpa [hEq b] using hb

theorem ntmUniqueAt_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    NTMUniqueAt M x t sigma hSat 0 := by
  refine {
    hState := ntmInitial_state_exists_unique M x t sigma hSat
    hHead := ntmInitial_head_exists_unique M x t sigma hSat
    hLeft := ?_
    hRight := ?_
  }
  · intro i hi
    exact ntmInitial_left_exists_unique M x t sigma hSat i hi
  · intro i hi
    exact ntmInitial_right_exists_unique M x t sigma hSat i hi

theorem ntmUniqueAt_halted_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hU : NTMUniqueAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    NTMUniqueAt M x t sigma hSat (s + 1) := by
  refine {
    hState := ?_
    hHead := ?_
    hLeft := ?_
    hRight := ?_
  }
  · exact existsUnique_of_exact_decide
      (fun r => sigma (ntmStateVar M t (s + 1) r)) q
      (ntmHalted_state_exact M x t s q a sigma hSat hs hq ha hHalt)
  · exact existsUnique_transport
      (fun b => sigma (ntmHeadVar M t s b))
      (fun b => sigma (ntmHeadVar M t (s + 1) b))
      hU.hHead
      (ntmHalted_head_copy M x t s q a sigma hSat hs hq ha hHalt)
  · intro i hi
    exact existsUnique_transport
      (fun b => sigma (ntmLeftVar M x t s i b))
      (fun b => sigma (ntmLeftVar M x t (s + 1) i b))
      (hU.hLeft i hi)
      (ntmHalted_left_copy M x t s q a sigma hSat hs hq ha hHalt i hi)
  · intro i hi
    exact existsUnique_transport
      (fun b => sigma (ntmRightVar M x t s i b))
      (fun b => sigma (ntmRightVar M x t (s + 1) i b))
      (hU.hRight i hi)
      (ntmHalted_right_copy M x t s q a sigma hSat hs hq ha hHalt i hi)


theorem ntmUniqueAt_active_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hU : NTMUniqueAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    NTMUniqueAt M x t sigma hSat (s + 1) := by
  rcases ntmChoice_exists_of_guard M x t s q a sigma hSat hs hq ha hActive with
    ⟨j, hj⟩
  rcases htr : (M.machine.transition q a).get j with ⟨qNext, write, d⟩
  have hStateExact :
      forall r : Fin (M.stateCount + 1),
        sigma (ntmStateVar M t (s + 1) r) = decide (r = qNext) := by
    simpa [htr] using
      ntmChoice_effect_state_exact M x t s q a j sigma hSat hs hActive hj
  have hrpos : 0 < ntmRadius x t := by
    simp [ntmRadius]
  cases d with
  | stay =>
      have hHeadExact :
          forall b : Option Bool,
            sigma (ntmHeadVar M t (s + 1) b) = decide (b = write) := by
        simpa [htr] using
          ntmChoice_effect_head_exact_stay M x t s q a j sigma
            hSat hs hActive (by simpa [htr]) hj
      refine {
        hState := existsUnique_of_exact_decide
          (fun r => sigma (ntmStateVar M t (s + 1) r)) qNext hStateExact
        hHead := existsUnique_of_exact_decide
          (fun b => sigma (ntmHeadVar M t (s + 1) b)) write hHeadExact
        hLeft := ?_
        hRight := ?_
      }
      · intro i hi
        exact existsUnique_transport
          (fun b => sigma (ntmLeftVar M x t s i b))
          (fun b => sigma (ntmLeftVar M x t (s + 1) i b))
          (hU.hLeft i hi)
          (by simpa [htr] using
            ntmStay_left_copy_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) i hi)
      · intro i hi
        exact existsUnique_transport
          (fun b => sigma (ntmRightVar M x t s i b))
          (fun b => sigma (ntmRightVar M x t (s + 1) i b))
          (hU.hRight i hi)
          (by simpa [htr] using
            ntmStay_right_copy_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) i hi)
  | left =>
      have hHeadCopy :
          forall b : Option Bool,
            sigma (ntmHeadVar M t (s + 1) b) =
              sigma (ntmLeftVar M x t s 0 b) := by
        simpa [htr] using
          ntmChoice_effect_head_exact_left M x t s q a j sigma
            hSat hs hActive (by simpa [htr]) hj
      refine {
        hState := existsUnique_of_exact_decide
          (fun r => sigma (ntmStateVar M t (s + 1) r)) qNext hStateExact
        hHead := existsUnique_transport
          (fun b => sigma (ntmLeftVar M x t s 0 b))
          (fun b => sigma (ntmHeadVar M t (s + 1) b))
          (hU.hLeft 0 hrpos) hHeadCopy
        hLeft := ?_
        hRight := ?_
      }
      · intro i hi
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hExact :
              forall b : Option Bool,
                sigma (ntmLeftVar M x t (s + 1) (ntmRadius x t - 1) b) =
                  decide (b = M.machine.blank) := by
            simpa [htr] using
              ntmLeft_blankLeft_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr])
          exact existsUnique_of_exact_decide
            (fun b => sigma (ntmLeftVar M x t (s + 1)
              (ntmRadius x t - 1) b))
            M.machine.blank hExact
        · have hi' : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          exact existsUnique_transport
            (fun b => sigma (ntmLeftVar M x t s (i + 1) b))
            (fun b => sigma (ntmLeftVar M x t (s + 1) i b))
            (hU.hLeft (i + 1) hip1)
            (by simpa [htr] using
              ntmLeft_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr]) i hi')
      · intro i hi
        by_cases hzero : i = 0
        · subst i
          have hExact :
              forall b : Option Bool,
                sigma (ntmRightVar M x t (s + 1) 0 b) =
                  decide (b = write) := by
            simpa [htr] using
              ntmLeft_writeRight0_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr])
          exact existsUnique_of_exact_decide
            (fun b => sigma (ntmRightVar M x t (s + 1) 0 b))
            write hExact
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
            use i - 1
            omega
          have hk : k < ntmRadius x t - 1 := by omega
          exact existsUnique_transport
            (fun b => sigma (ntmRightVar M x t s k b))
            (fun b => sigma (ntmRightVar M x t (s + 1) (k + 1) b))
            (hU.hRight k (by omega))
            (by simpa [htr] using
              ntmLeft_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr]) k hk)
  | right =>
      have hHeadCopy :
          forall b : Option Bool,
            sigma (ntmHeadVar M t (s + 1) b) =
              sigma (ntmRightVar M x t s 0 b) := by
        simpa [htr] using
          ntmChoice_effect_head_exact_right M x t s q a j sigma
            hSat hs hActive (by simpa [htr]) hj
      refine {
        hState := existsUnique_of_exact_decide
          (fun r => sigma (ntmStateVar M t (s + 1) r)) qNext hStateExact
        hHead := existsUnique_transport
          (fun b => sigma (ntmRightVar M x t s 0 b))
          (fun b => sigma (ntmHeadVar M t (s + 1) b))
          (hU.hRight 0 hrpos) hHeadCopy
        hLeft := ?_
        hRight := ?_
      }
      · intro i hi
        by_cases hzero : i = 0
        · subst i
          have hExact :
              forall b : Option Bool,
                sigma (ntmLeftVar M x t (s + 1) 0 b) =
                  decide (b = write) := by
            simpa [htr] using
              ntmRight_writeLeft0_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr])
          exact existsUnique_of_exact_decide
            (fun b => sigma (ntmLeftVar M x t (s + 1) 0 b))
            write hExact
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
            use i - 1
            omega
          have hk : k < ntmRadius x t - 1 := by omega
          exact existsUnique_transport
            (fun b => sigma (ntmLeftVar M x t s k b))
            (fun b => sigma (ntmLeftVar M x t (s + 1) (k + 1) b))
            (hU.hLeft k (by omega))
            (by simpa [htr] using
              ntmRight_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr]) k hk)
      · intro i hi
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hExact :
              forall b : Option Bool,
                sigma (ntmRightVar M x t (s + 1) (ntmRadius x t - 1) b) =
                  decide (b = M.machine.blank) := by
            simpa [htr] using
              ntmRight_blankRight_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr])
          exact existsUnique_of_exact_decide
            (fun b => sigma (ntmRightVar M x t (s + 1)
              (ntmRadius x t - 1) b))
            M.machine.blank hExact
        · have hi' : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          exact existsUnique_transport
            (fun b => sigma (ntmRightVar M x t s (i + 1) b))
            (fun b => sigma (ntmRightVar M x t (s + 1) i b))
            (hU.hRight (i + 1) hip1)
            (by simpa [htr] using
              ntmRight_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
                (by simpa [htr]) i hi')


theorem ntmUniqueAt_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall s : Nat, s <= t ->
      NTMUniqueAt M x t sigma hSat s := by
  intro s
  induction s with
  | zero =>
      intro _
      exact ntmUniqueAt_zero M x t sigma hSat
  | succ s ih =>
      intro hsle
      have hslt : s < t := by omega
      have hU : NTMUniqueAt M x t sigma hSat s :=
        ih (by omega)
      rcases hU.hState with ⟨q, hq, hqUnique⟩
      rcases hU.hHead with ⟨a, ha, haUnique⟩
      by_cases hHalt :
          M.machine.accepting q = true ∨
            M.machine.rejecting q = true
      · exact ntmUniqueAt_halted_step M x t s sigma hSat hslt hU
          q a hq ha hHalt
      · have hAcc : M.machine.accepting q = false := by
          cases h : M.machine.accepting q with
          | false => rfl
          | true =>
              exact False.elim (hHalt (Or.inl h))
        have hRej : M.machine.rejecting q = false := by
          cases h : M.machine.rejecting q with
          | false => rfl
          | true =>
              exact False.elim (hHalt (Or.inr h))
        exact ntmUniqueAt_active_step M x t s sigma hSat hslt hU
          q a hq ha ⟨hAcc, hRej⟩


noncomputable def decodeState
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    Fin (M.stateCount + 1) :=
  (ntmUniqueAt_all M x t sigma hSat s hs).hState.choose

noncomputable def decodeHead
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    Option Bool :=
  (ntmUniqueAt_all M x t sigma hSat s hs).hHead.choose

noncomputable def decodeLeftCell
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t) :
    Option Bool :=
  ((ntmUniqueAt_all M x t sigma hSat s hs).hLeft i hi).choose

noncomputable def decodeRightCell
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t) :
    Option Bool :=
  ((ntmUniqueAt_all M x t sigma hSat s hs).hRight i hi).choose

def trimTrailingBlank
    (blank : Option Bool) (xs : List (Option Bool)) : List (Option Bool) :=
  (xs.reverse.dropWhile (fun a => decide (a = blank))).reverse

noncomputable def decodeLeftList
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : List (Option Bool) :=
  trimTrailingBlank M.machine.blank
    (rawLeftList M x t sigma hSat s hs)

noncomputable def decodeRightList
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : List (Option Bool) :=
  trimTrailingBlank M.machine.blank
    (rawRightList M x t sigma hSat s hs)

noncomputable def decodeConfig
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : NTMConfig M :=
  { state := decodeState M x t sigma hSat s hs
    tape :=
      { left := decodeLeftList M x t sigma hSat s hs
        head := decodeHead M x t sigma hSat s hs
        right := decodeRightList M x t sigma hSat s hs } }

theorem decodeState_true
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    sigma (ntmStateVar M t s (decodeState M x t sigma hSat s hs)) = true := by
  exact (ntmUniqueAt_all M x t sigma hSat s hs).hState.choose_spec.1

theorem decodeState_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (r : Fin (M.stateCount + 1))
    (hr : sigma (ntmStateVar M t s r) = true) :
    r = decodeState M x t sigma hSat s hs := by
  exact (ntmUniqueAt_all M x t sigma hSat s hs).hState.choose_spec.2 r hr

theorem decodeHead_true
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    sigma (ntmHeadVar M t s (decodeHead M x t sigma hSat s hs)) = true := by
  exact (ntmUniqueAt_all M x t sigma hSat s hs).hHead.choose_spec.1

theorem decodeHead_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (a : Option Bool)
    (ha : sigma (ntmHeadVar M t s a) = true) :
    a = decodeHead M x t sigma hSat s hs := by
  exact (ntmUniqueAt_all M x t sigma hSat s hs).hHead.choose_spec.2 a ha

theorem decodeLeftCell_true
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t) :
    sigma (ntmLeftVar M x t s i
      (decodeLeftCell M x t sigma hSat s hs i hi)) = true := by
  exact ((ntmUniqueAt_all M x t sigma hSat s hs).hLeft i hi).choose_spec.1

theorem decodeLeftCell_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t)
    (b : Option Bool)
    (hb : sigma (ntmLeftVar M x t s i b) = true) :
    b = decodeLeftCell M x t sigma hSat s hs i hi := by
  exact ((ntmUniqueAt_all M x t sigma hSat s hs).hLeft i hi).choose_spec.2 b hb

theorem decodeRightCell_true
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t) :
    sigma (ntmRightVar M x t s i
      (decodeRightCell M x t sigma hSat s hs i hi)) = true := by
  exact ((ntmUniqueAt_all M x t sigma hSat s hs).hRight i hi).choose_spec.1

theorem decodeRightCell_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t)
    (b : Option Bool)
    (hb : sigma (ntmRightVar M x t s i b) = true) :
    b = decodeRightCell M x t sigma hSat s hs i hi := by
  exact ((ntmUniqueAt_all M x t sigma hSat s hs).hRight i hi).choose_spec.2 b hb

@[simp] theorem decodeConfig_state
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    (decodeConfig M x t sigma hSat s hs).state =
      decodeState M x t sigma hSat s hs := by
  rfl

@[simp] theorem decodeConfig_head
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    (decodeConfig M x t sigma hSat s hs).tape.head =
      decodeHead M x t sigma hSat s hs := by
  rfl


theorem trimTrailingBlank_append_blank
    (blank : Option Bool) (xs : List (Option Bool)) :
    trimTrailingBlank blank (xs ++ [blank]) =
      trimTrailingBlank blank xs := by
  simp [trimTrailingBlank, List.reverse_append]

theorem trimTrailingBlank_nil
    (blank : Option Bool) :
    trimTrailingBlank blank [] = [] := by
  simp [trimTrailingBlank]

theorem trimTrailingBlank_all_blank
    (blank : Option Bool) (n : Nat) :
    trimTrailingBlank blank (List.replicate n blank) = [] := by
  induction n with
  | zero =>
      simp [trimTrailingBlank]
  | succ n ih =>
      rw [List.replicate_succ]
      rw [trimTrailingBlank_append_blank]
      exact ih

noncomputable def rawLeftList
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : List (Option Bool) :=
  List.ofFn (fun i : Fin (ntmRadius x t) =>
    decodeLeftCell M x t sigma hSat s hs i.val i.isLt)

noncomputable def rawRightList
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : List (Option Bool) :=
  List.ofFn (fun i : Fin (ntmRadius x t) =>
    decodeRightCell M x t sigma hSat s hs i.val i.isLt)

theorem decodeLeftList_eq_trim_raw
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    decodeLeftList M x t sigma hSat s hs =
      trimTrailingBlank M.machine.blank
        (rawLeftList M x t sigma hSat s hs) := by
  rfl

theorem decodeRightList_eq_trim_raw
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    decodeRightList M x t sigma hSat s hs =
      trimTrailingBlank M.machine.blank
        (rawRightList M x t sigma hSat s hs) := by
  rfl

theorem rawLeftList_length
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    (rawLeftList M x t sigma hSat s hs).length = ntmRadius x t := by
  simp [rawLeftList]

theorem rawRightList_length
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) :
    (rawRightList M x t sigma hSat s hs).length = ntmRadius x t := by
  simp [rawRightList]

theorem rawLeftList_get
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Fin (ntmRadius x t)) :
    (rawLeftList M x t sigma hSat s hs).get i =
      decodeLeftCell M x t sigma hSat s hs i.val i.isLt := by
  simp [rawLeftList]

theorem rawRightList_get
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t)
    (i : Fin (ntmRadius x t)) :
    (rawRightList M x t sigma hSat s hs).get i =
      decodeRightCell M x t sigma hSat s hs i.val i.isLt := by
  simp [rawRightList]


theorem rawLeftList_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    rawLeftList M x t sigma hSat (s + 1) (by omega) =
      rawLeftList M x t sigma hSat s (by omega) := by
  unfold rawLeftList
  apply congrArg List.ofFn
  funext i
  have hOld := decodeLeftCell_true M x t sigma hSat s (by omega) i.val i.isLt
  have hEq := ntmStay_left_copy_exact M x t s q a j sigma hSat hs hActive hj hDir i.val i.isLt
  have hNew :
      sigma (ntmLeftVar M x t (s + 1) i.val
        (decodeLeftCell M x t sigma hSat s (by omega) i.val i.isLt)) = true := by
    rw [hEq]
    exact hOld
  exact (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
    i.val i.isLt
    (decodeLeftCell M x t sigma hSat s (by omega) i.val i.isLt)
    hNew).symm

theorem rawRightList_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    rawRightList M x t sigma hSat (s + 1) (by omega) =
      rawRightList M x t sigma hSat s (by omega) := by
  unfold rawRightList
  apply congrArg List.ofFn
  funext i
  have hOld := decodeRightCell_true M x t sigma hSat s (by omega) i.val i.isLt
  have hEq := ntmStay_right_copy_exact M x t s q a j sigma hSat hs hActive hj hDir i.val i.isLt
  have hNew :
      sigma (ntmRightVar M x t (s + 1) i.val
        (decodeRightCell M x t sigma hSat s (by omega) i.val i.isLt)) = true := by
    rw [hEq]
    exact hOld
  exact (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
    i.val i.isLt
    (decodeRightCell M x t sigma hSat s (by omega) i.val i.isLt)
    hNew).symm

theorem decodeLeftList_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    decodeLeftList M x t sigma hSat (s + 1) (by omega) =
      decodeLeftList M x t sigma hSat s (by omega) := by
  simp only [decodeLeftList_eq_trim_raw]
  rw [rawLeftList_stay M x t s sigma hSat hs q a j hActive hj hDir]

theorem decodeRightList_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    decodeRightList M x t sigma hSat (s + 1) (by omega) =
      decodeRightList M x t sigma hSat s (by omega) := by
  simp only [decodeRightList_eq_trim_raw]
  rw [rawRightList_stay M x t s sigma hSat hs q a j hActive hj hDir]

theorem decodeHead_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    decodeHead M x t sigma hSat (s + 1) (by omega) =
      ((M.machine.transition q a).get j).2.1 := by
  let write := ((M.machine.transition q a).get j).2.1
  have hExact := ntmChoice_effect_head_exact_stay M x t s q a j sigma
    hSat hs hActive hDir hj
  have htrue :
      sigma (ntmHeadVar M t (s + 1) write) = true := by
    simpa [write] using hExact write
  exact (decodeHead_unique M x t sigma hSat (s + 1) (by omega) write htrue).symm

theorem decodeState_choice
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    decodeState M x t sigma hSat (s + 1) (by omega) =
      ((M.machine.transition q a).get j).1 := by
  let qNext := ((M.machine.transition q a).get j).1
  have hExact := ntmChoice_effect_state_exact M x t s q a j sigma hSat hs hActive hj
  have htrue :
      sigma (ntmStateVar M t (s + 1) qNext) = true := by
    simpa [qNext] using hExact qNext
  exact (decodeState_unique M x t sigma hSat (s + 1) (by omega) qNext htrue).symm

theorem decodeTape_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay) :
    (decodeConfig M x t sigma hSat (s + 1) (by omega)).tape =
      Tape.move M.machine.blank Direction.stay
        ((decodeConfig M x t sigma hSat s (by omega)).tape.write
          ((M.machine.transition q a).get j).2.1) := by
  apply Tape.ext
  · simpa [decodeConfig, Tape.write, Tape.move] using
      decodeLeftList_stay M x t s sigma hSat hs q a j hActive hj hDir
  · simpa [decodeConfig, Tape.write, Tape.move] using
      decodeHead_stay M x t s sigma hSat hs q a j hActive hj hDir
  · simpa [decodeConfig, Tape.write, Tape.move] using
      decodeRightList_stay M x t s sigma hSat hs q a j hActive hj hDir


theorem list_getD_eq_default_of_length_le
    {α : Type} (xs : List α) (d : α) (i : Nat)
    (h : xs.length <= i) :
    xs.getD i d = d := by
  induction xs generalizing i with
  | nil =>
      simp
  | cons a as ih =>
      cases i with
      | zero =>
          simp at h
      | succ i =>
          simp [List.getD_cons_succ]
          apply ih
          simpa using Nat.succ_le_succ_iff.mp h

structure NTMPaddingAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) : Prop where
  leftBlank :
    forall i : Nat,
      x.length + s <= i ->
      i < ntmRadius x t ->
      sigma (ntmLeftVar M x t s i M.machine.blank) = true
  rightBlank :
    forall i : Nat,
      x.length + s <= i ->
      i < ntmRadius x t ->
      sigma (ntmRightVar M x t s i M.machine.blank) = true

theorem ntmPaddingAt_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    NTMPaddingAt M x t sigma hSat 0 := by
  refine { leftBlank := ?_, rightBlank := ?_ }
  · intro i hi hRadius
    have hExact :=
      ntmInitial_left_exact M x t sigma hSat i hRadius M.machine.blank
    have htarget :
        (inputTape x).left.getD i M.machine.blank = M.machine.blank := by
      cases x <;> simp [inputTape]
    simpa [htarget] using hExact
  · intro i hi hRadius
    have hExact :=
      ntmInitial_right_exact M x t sigma hSat i hRadius M.machine.blank
    have htarget :
        (inputTape x).right.getD i M.machine.blank = M.machine.blank := by
      cases x with
      | nil =>
          simp [inputTape]
      | cons b bs =>
          simp only [inputTape]
          apply list_getD_eq_default_of_length_le
          simpa using hi
    simpa [htarget] using hExact

theorem ntmPaddingAt_halted_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hP : NTMPaddingAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    NTMPaddingAt M x t sigma hSat (s + 1) := by
  refine { leftBlank := ?_, rightBlank := ?_ }
  · intro i hi hRadius
    have hOld : sigma (ntmLeftVar M x t s i M.machine.blank) = true :=
      hP.leftBlank i (by omega) hRadius
    have hCopy :=
      ntmHalted_left_copy M x t s q a sigma hSat hs hq ha hHalt i hRadius
        M.machine.blank
    simpa [hCopy] using hOld
  · intro i hi hRadius
    have hOld : sigma (ntmRightVar M x t s i M.machine.blank) = true :=
      hP.rightBlank i (by omega) hRadius
    have hCopy :=
      ntmHalted_right_copy M x t s q a sigma hSat hs hq ha hHalt i hRadius
        M.machine.blank
    simpa [hCopy] using hOld


structure NTMBlankTailAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) : Prop where
  hLeft :
    forall i : Nat,
      x.length + s <= i ->
      i < ntmRadius x t ->
      sigma (ntmLeftVar M x t s i M.machine.blank) = true
  hRight :
    forall i : Nat,
      x.length + s <= i ->
      i < ntmRadius x t ->
      sigma (ntmRightVar M x t s i M.machine.blank) = true

theorem ntmBlankTailAt_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    NTMBlankTailAt M x t sigma hSat 0 := by
  refine { hLeft := ?_, hRight := ?_ }
  · intro i hxi hir
    have hExact := ntmInitial_left_exact M x t sigma hSat i hir M.machine.blank
    have hget :
        (inputTape x).left.getD i M.machine.blank = M.machine.blank := by
      cases x <;> simp [inputTape]
    simpa [hget] using hExact
  · intro i hxi hir
    have hExact := ntmInitial_right_exact M x t sigma hSat i hir M.machine.blank
    have hget :
        (inputTape x).right.getD i M.machine.blank = M.machine.blank := by
      cases x with
      | nil =>
          simp [inputTape]
      | cons b bs =>
          simp [inputTape]
          have hi : bs.length <= i := by
            simpa using hxi
          exact list_getD_eq_default_of_length_le _ _ hi
    simpa [hget] using hExact

theorem ntmBlankTail_boundary
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hB : NTMBlankTailAt M x t sigma hSat s) :
    sigma (ntmLeftVar M x t s (ntmRadius x t - 1) M.machine.blank) = true ∧
    sigma (ntmRightVar M x t s (ntmRadius x t - 1) M.machine.blank) = true := by
  have hidx : x.length + s <= ntmRadius x t - 1 := by
    simp [ntmRadius]
    omega
  have hlt : ntmRadius x t - 1 < ntmRadius x t := by
    simp [ntmRadius]
  exact ⟨hB.hLeft _ hidx hlt, hB.hRight _ hidx hlt⟩

theorem ntmBlankTail_penultimate
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hB : NTMBlankTailAt M x t sigma hSat s) :
    sigma (ntmLeftVar M x t s (ntmRadius x t - 2) M.machine.blank) = true ∧
    sigma (ntmRightVar M x t s (ntmRadius x t - 2) M.machine.blank) = true := by
  have hidx : x.length + s <= ntmRadius x t - 2 := by
    simp [ntmRadius]
    omega
  have hlt : ntmRadius x t - 2 < ntmRadius x t := by
    simp [ntmRadius]
  exact ⟨hB.hLeft _ hidx hlt, hB.hRight _ hidx hlt⟩


theorem ntmPaddingAt_active_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hP : NTMPaddingAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    NTMPaddingAt M x t sigma hSat (s + 1) := by
  rcases ntmChoice_exists_of_guard M x t s q a sigma hSat hs hq ha hActive with
    ⟨j, hj⟩
  rcases htr : (M.machine.transition q a).get j with ⟨qNext, write, d⟩
  cases d with
  | stay =>
      refine { leftBlank := ?_, rightBlank := ?_ }
      · intro i hi hRadius
        have hOld := hP.leftBlank i (by omega) hRadius
        have hCopy :=
          ntmStay_left_copy_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) i hRadius M.machine.blank
        simpa [hCopy] using hOld
      · intro i hi hRadius
        have hOld := hP.rightBlank i (by omega) hRadius
        have hCopy :=
          ntmStay_right_copy_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) i hRadius M.machine.blank
        simpa [hCopy] using hOld
  | left =>
      refine { leftBlank := ?_, rightBlank := ?_ }
      · intro i hi hRadius
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hExact :=
            ntmLeft_blankLeft_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) M.machine.blank
          simpa using hExact
        · have hiShift : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          have hOld := hP.leftBlank (i + 1) (by omega) hip1
          have hCopy :=
            ntmLeft_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) i hiShift M.machine.blank
          simpa [hCopy] using hOld
      · intro i hi hRadius
        have hne0 : i ≠ 0 := by
          intro hzero
          subst i
          omega
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
          use i - 1
          omega
        have hk : k < ntmRadius x t - 1 := by omega
        have hOld := hP.rightBlank k (by omega) (by omega)
        have hCopy :=
          ntmLeft_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) k hk M.machine.blank
        simpa [hCopy] using hOld
  | right =>
      refine { leftBlank := ?_, rightBlank := ?_ }
      · intro i hi hRadius
        have hne0 : i ≠ 0 := by
          intro hzero
          subst i
          omega
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
          use i - 1
          omega
        have hk : k < ntmRadius x t - 1 := by omega
        have hOld := hP.leftBlank k (by omega) (by omega)
        have hCopy :=
          ntmRight_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) k hk M.machine.blank
        simpa [hCopy] using hOld
      · intro i hi hRadius
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hExact :=
            ntmRight_blankRight_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) M.machine.blank
          simpa using hExact
        · have hiShift : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          have hOld := hP.rightBlank (i + 1) (by omega) hip1
          have hCopy :=
            ntmRight_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
              (by simpa [htr]) i hiShift M.machine.blank
          simpa [hCopy] using hOld

theorem ntmPaddingAt_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall s : Nat, s <= t ->
      NTMPaddingAt M x t sigma hSat s := by
  intro s
  induction s with
  | zero =>
      intro _
      exact ntmPaddingAt_zero M x t sigma hSat
  | succ s ih =>
      intro hsle
      have hslt : s < t := by omega
      have hP := ih (by omega)
      have hU := ntmUniqueAt_all M x t sigma hSat s (by omega)
      rcases hU.hState with ⟨q, hq, hqU⟩
      rcases hU.hHead with ⟨a, ha, haU⟩
      by_cases hHalt :
          M.machine.accepting q = true ∨ M.machine.rejecting q = true
      · exact ntmPaddingAt_halted_step M x t s sigma hSat hslt hP
          q a hq ha hHalt
      · have hAcc : M.machine.accepting q = false := by
          cases h : M.machine.accepting q with
          | false => rfl
          | true => exact False.elim (hHalt (Or.inl h))
        have hRej : M.machine.rejecting q = false := by
          cases h : M.machine.rejecting q with
          | false => rfl
          | true => exact False.elim (hHalt (Or.inr h))
        exact ntmPaddingAt_active_step M x t s sigma hSat hslt hP
          q a hq ha ⟨hAcc, hRej⟩


theorem ntmBlankTailAt_halted_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hB : NTMBlankTailAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    NTMBlankTailAt M x t sigma hSat (s + 1) := by
  refine { hLeft := ?_, hRight := ?_ }
  · intro i hxi hir
    have hold : sigma (ntmLeftVar M x t s i M.machine.blank) = true :=
      hB.hLeft i (by omega) hir
    have hcopy := ntmHalted_left_copy M x t s q a sigma hSat hs hq ha hHalt i hir
    rw [hcopy]
    exact hold
  · intro i hxi hir
    have hold : sigma (ntmRightVar M x t s i M.machine.blank) = true :=
      hB.hRight i (by omega) hir
    have hcopy := ntmHalted_right_copy M x t s q a sigma hSat hs hq ha hHalt i hir
    rw [hcopy]
    exact hold

theorem ntmBlankTailAt_active_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hB : NTMBlankTailAt M x t sigma hSat s)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    NTMBlankTailAt M x t sigma hSat (s + 1) := by
  rcases ntmChoice_exists_of_guard M x t s q a sigma hSat hs hq ha hActive with ⟨j, hj⟩
  rcases htr : (M.machine.transition q a).get j with ⟨qNext, write, d⟩
  cases d with
  | stay =>
      refine { hLeft := ?_, hRight := ?_ }
      · intro i hxi hir
        have hold := hB.hLeft i (by omega) hir
        have hcopy := ntmStay_left_copy_exact M x t s q a j sigma hSat hs hActive hj
          (by simpa [htr]) i hir
        rw [hcopy]
        exact hold
      · intro i hxi hir
        have hold := hB.hRight i (by omega) hir
        have hcopy := ntmStay_right_copy_exact M x t s q a j sigma hSat hs hActive hj
          (by simpa [htr]) i hir
        rw [hcopy]
        exact hold
  | left =>
      refine { hLeft := ?_, hRight := ?_ }
      · intro i hxi hir
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hex := ntmLeft_blankLeft_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr])
          simpa using hex M.machine.blank
        · have hi : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          have hold := hB.hLeft (i + 1) (by omega) hip1
          have hcopy := ntmLeft_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) i hi
          rw [hcopy]
          exact hold
      · intro i hxi hir
        have hne0 : i ≠ 0 := by
          intro h0
          subst i
          simp at hxi
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
          use i - 1
          omega
        have hk : k < ntmRadius x t - 1 := by omega
        have hold := hB.hRight k (by omega) (by omega)
        have hcopy := ntmLeft_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
          (by simpa [htr]) k hk
        rw [hcopy]
        exact hold
  | right =>
      refine { hLeft := ?_, hRight := ?_ }
      · intro i hxi hir
        have hne0 : i ≠ 0 := by
          intro h0
          subst i
          simp at hxi
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
          use i - 1
          omega
        have hk : k < ntmRadius x t - 1 := by omega
        have hold := hB.hLeft k (by omega) (by omega)
        have hcopy := ntmRight_shiftedLeft_exact M x t s q a j sigma hSat hs hActive hj
          (by simpa [htr]) k hk
        rw [hcopy]
        exact hold
      · intro i hxi hir
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hex := ntmRight_blankRight_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr])
          simpa using hex M.machine.blank
        · have hi : i < ntmRadius x t - 1 := by omega
          have hip1 : i + 1 < ntmRadius x t := by omega
          have hold := hB.hRight (i + 1) (by omega) hip1
          have hcopy := ntmRight_shiftedRight_exact M x t s q a j sigma hSat hs hActive hj
            (by simpa [htr]) i hi
          rw [hcopy]
          exact hold

theorem ntmBlankTailAt_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall s : Nat, s <= t -> NTMBlankTailAt M x t sigma hSat s := by
  intro s
  induction s with
  | zero =>
      intro _
      exact ntmBlankTailAt_zero M x t sigma hSat
  | succ s ih =>
      intro hsle
      have hslt : s < t := by omega
      have hB := ih (by omega)
      have hU := ntmUniqueAt_all M x t sigma hSat s (by omega)
      rcases hU.hState with ⟨q, hq, _⟩
      rcases hU.hHead with ⟨a, ha, _⟩
      by_cases hHalt :
          M.machine.accepting q = true ∨ M.machine.rejecting q = true
      · exact ntmBlankTailAt_halted_step M x t s sigma hSat hslt hB q a hq ha hHalt
      · have hAcc : M.machine.accepting q = false := by
          cases h : M.machine.accepting q with
          | false => rfl
          | true => exact False.elim (hHalt (Or.inl h))
        have hRej : M.machine.rejecting q = false := by
          cases h : M.machine.rejecting q with
          | false => rfl
          | true => exact False.elim (hHalt (Or.inr h))
        exact ntmBlankTailAt_active_step M x t s sigma hSat hslt hB q a hq ha ⟨hAcc, hRej⟩


theorem list_eq_of_length_getD
    {α : Type} (d : α) {xs ys : List α}
    (hlen : xs.length = ys.length)
    (hget : forall i : Nat, i < xs.length -> xs.getD i d = ys.getD i d) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp at hlen ⊢
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          have hxy : x = y := by
            have h0 := hget 0 (by simp)
            simpa using h0
          have hlen' : xs.length = ys.length := by
            simpa using hlen
          have htail :
              forall i : Nat, i < xs.length ->
                xs.getD i d = ys.getD i d := by
            intro i hi
            have hs := hget (i + 1) (by simp [hi])
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs
          subst y
          simp [ih hlen' htail]

theorem rawLeftList_left_shape
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left) :
    rawLeftList M x t sigma hSat (s + 1) (by omega) =
      (rawLeftList M x t sigma hSat s (by omega)).drop 1 ++
        [M.machine.blank] := by
  apply list_eq_of_length_getD M.machine.blank
  · simp [rawLeftList_length, ntmRadius]
  · intro i hi
    have hir : i < ntmRadius x t := by
      simpa [rawLeftList_length] using hi
    by_cases hlast : i = ntmRadius x t - 1
    · subst i
      have hExact := ntmLeft_blankLeft_exact M x t s q a j sigma
        hSat hs hActive hj hDir
      have hblank :
          decodeLeftCell M x t sigma hSat (s + 1) (by omega)
            (ntmRadius x t - 1) (by omega) = M.machine.blank := by
        apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
          (ntmRadius x t - 1) (by omega) M.machine.blank)
        simpa using hExact M.machine.blank
      simp [rawLeftList, hblank, rawLeftList_length, ntmRadius]
    · have hiShift : i < ntmRadius x t - 1 := by omega
      have hiOld : i + 1 < ntmRadius x t := by omega
      have hOld := decodeLeftCell_true M x t sigma hSat s (by omega)
        (i + 1) hiOld
      have hEq := ntmLeft_shiftedLeft_exact M x t s q a j sigma
        hSat hs hActive hj hDir i hiShift
      have hNew :
          sigma (ntmLeftVar M x t (s + 1) i
            (decodeLeftCell M x t sigma hSat s (by omega)
              (i + 1) hiOld)) = true := by
        rw [hEq]
        exact hOld
      have hcell :
          decodeLeftCell M x t sigma hSat (s + 1) (by omega) i hir =
            decodeLeftCell M x t sigma hSat s (by omega) (i + 1) hiOld := by
        exact (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
          i hir _ hNew).symm
      simp [rawLeftList, List.getD_drop, hcell, hiShift, ntmRadius]

theorem rawRightList_left_shape
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left) :
    rawRightList M x t sigma hSat (s + 1) (by omega) =
      ((M.machine.transition q a).get j).2.1 ::
        (rawRightList M x t sigma hSat s (by omega)).take
          (ntmRadius x t - 1) := by
  apply list_eq_of_length_getD M.machine.blank
  · simp [rawRightList_length, ntmRadius]
  · intro i hi
    have hir : i < ntmRadius x t := by
      simpa [rawRightList_length] using hi
    cases i with
    | zero =>
        have hExact := ntmLeft_writeRight0_exact M x t s q a j sigma
          hSat hs hActive hj hDir
        have hwrite :
            decodeRightCell M x t sigma hSat (s + 1) (by omega) 0 (by omega) =
              ((M.machine.transition q a).get j).2.1 := by
          apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
            0 (by omega) ((M.machine.transition q a).get j).2.1)
          simpa using hExact ((M.machine.transition q a).get j).2.1
        simp [rawRightList, hwrite]
    | succ k =>
        have hk : k < ntmRadius x t - 1 := by omega
        have hkOld : k < ntmRadius x t := by omega
        have hOld := decodeRightCell_true M x t sigma hSat s (by omega) k hkOld
        have hEq := ntmLeft_shiftedRight_exact M x t s q a j sigma
          hSat hs hActive hj hDir k hk
        have hNew :
            sigma (ntmRightVar M x t (s + 1) (k + 1)
              (decodeRightCell M x t sigma hSat s (by omega) k hkOld)) = true := by
          rw [hEq]
          exact hOld
        have hcell :
            decodeRightCell M x t sigma hSat (s + 1) (by omega)
              (k + 1) hir =
                decodeRightCell M x t sigma hSat s (by omega) k hkOld := by
          exact (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
            (k + 1) hir _ hNew).symm
        simp [rawRightList, hcell, hk, ntmRadius]


/-- Structural warning: canonical trimming is not equal to the concrete Tape
    representation after a move.  A written blank is still an explicit list
    cell in Model.Tape.move, whereas trimTrailingBlank removes it. -/
theorem trimTrailingBlank_does_not_preserve_explicit_blank :
    trimTrailingBlank none [none] = [] := by
  simp [trimTrailingBlank]

/-- Concrete witness for the failed canonical-tape route:
    moving left after writing blank can leave one explicit blank on the right. -/
theorem tapeMove_left_can_create_explicit_blank :
    (Tape.move none Direction.left
      (({ left := [some true], head := some false, right := [] } :
          Tape (Option Bool)).write none)).right = [none] := by
  rfl

/-- Therefore the trimmed representation of the same right-cell values is
    structurally different from the Tape.move result. -/
theorem trim_route_left_counterexample :
    trimTrailingBlank none
      (Tape.move none Direction.left
        (({ left := [some true], head := some false, right := [] } :
            Tape (Option Bool)).write none)).right
      ≠
    (Tape.move none Direction.left
      (({ left := [some true], head := some false, right := [] } :
          Tape (Option Bool)).write none)).right := by
  simp [trimTrailingBlank, Tape.write, Tape.move]



noncomputable def decodeChoiceIndex
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    Fin (M.machine.transition q a).length :=
  (ntmChoice_exists_of_guard M x t s q a sigma hSat hs hq ha hActive).choose

theorem decodeChoiceIndex_true
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive : M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    sigma
      (ntmChoiceVar M x t s q a
        (decodeChoiceIndex M x t s sigma hSat hs q a hq ha hActive).val) = true := by
  exact (ntmChoice_exists_of_guard M x t s q a sigma hSat hs hq ha hActive).choose_spec

noncomputable def operationalDecodeConfig
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    (s : Nat) -> s <= t -> NTMConfig M
  | 0, _ =>
      initialNTMConfig M.machine x
  | s + 1, hsle =>
      let hs : s < t := by omega
      let hsPrev : s <= t := by omega
      let prev := operationalDecodeConfig M x t sigma hSat s hsPrev
      let q := decodeState M x t sigma hSat s hsPrev
      let a := decodeHead M x t sigma hSat s hsPrev
      if hHalt :
          M.machine.accepting q = true ∨ M.machine.rejecting q = true then
        prev
      else
        let hActive :
            M.machine.accepting q = false ∧ M.machine.rejecting q = false := by
          constructor
          · cases h : M.machine.accepting q with
            | false => rfl
            | true => exact False.elim (hHalt (Or.inl h))
          · cases h : M.machine.rejecting q with
            | false => rfl
            | true => exact False.elim (hHalt (Or.inr h))
        let hq := decodeState_true M x t sigma hSat s hsPrev
        let ha := decodeHead_true M x t sigma hSat s hsPrev
        let j := decodeChoiceIndex M x t s sigma hSat hs q a hq ha hActive
        M.machine.stepBranch prev ((M.machine.transition q a).get j)

@[simp] theorem operationalDecodeConfig_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    operationalDecodeConfig M x t sigma hSat 0 (by omega) =
      initialNTMConfig M.machine x := by
  rfl


theorem tapeMove_stay_head
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.stay (tape.write write)).head = write := by
  rfl

theorem tapeMove_stay_left_getD
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.stay (tape.write write)).left.getD i blank =
      tape.left.getD i blank := by
  rfl

theorem tapeMove_stay_right_getD
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.stay (tape.write write)).right.getD i blank =
      tape.right.getD i blank := by
  rfl

theorem tapeMove_left_head
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.left (tape.write write)).head =
      tape.left.getD 0 blank := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.write, Tape.move]

theorem tapeMove_left_left_getD
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.left (tape.write write)).left.getD i blank =
      tape.left.getD (i + 1) blank := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.write, Tape.move, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem tapeMove_left_right_zero
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.left (tape.write write)).right.getD 0 blank =
      write := by
  cases tape <;> simp [Tape.write, Tape.move]

theorem tapeMove_left_right_succ
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.left (tape.write write)).right.getD (i + 1) blank =
      tape.right.getD i blank := by
  cases tape <;> simp [Tape.write, Tape.move, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem tapeMove_right_head
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.right (tape.write write)).head =
      tape.right.getD 0 blank := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.write, Tape.move]

theorem tapeMove_right_left_zero
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.right (tape.write write)).left.getD 0 blank =
      write := by
  cases tape <;> simp [Tape.write, Tape.move]

theorem tapeMove_right_left_succ
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.right (tape.write write)).left.getD (i + 1) blank =
      tape.left.getD i blank := by
  cases tape <;> simp [Tape.write, Tape.move, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem tapeMove_right_right_getD
    (blank write : Option Bool) (tape : Tape (Option Bool)) (i : Nat) :
    (Tape.move blank Direction.right (tape.write write)).right.getD i blank =
      tape.right.getD (i + 1) blank := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.write, Tape.move, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]


structure OperationalDecodeAgreesAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : Prop where
  hState :
    (operationalDecodeConfig M x t sigma hSat s hs).state =
      decodeState M x t sigma hSat s hs
  hHead :
    (operationalDecodeConfig M x t sigma hSat s hs).tape.head =
      decodeHead M x t sigma hSat s hs
  hLeft :
    forall i : Nat, i < ntmRadius x t ->
      (operationalDecodeConfig M x t sigma hSat s hs).tape.left.getD
          i M.machine.blank =
        decodeLeftCell M x t sigma hSat s hs i (by assumption)
  hRight :
    forall i : Nat, i < ntmRadius x t ->
      (operationalDecodeConfig M x t sigma hSat s hs).tape.right.getD
          i M.machine.blank =
        decodeRightCell M x t sigma hSat s hs i (by assumption)

theorem decodeInitial_state
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    M.machine.initial = decodeState M x t sigma hSat 0 (by omega) := by
  apply decodeState_unique M x t sigma hSat 0 (by omega)
  have hExact := ntmInitial_state_exact M x t sigma hSat M.machine.initial
  simpa using hExact

theorem decodeInitial_head
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    (inputTape x).head = decodeHead M x t sigma hSat 0 (by omega) := by
  apply decodeHead_unique M x t sigma hSat 0 (by omega)
  have hExact := ntmInitial_head_exact M x t sigma hSat (inputTape x).head
  simpa using hExact

theorem decodeInitial_leftCell
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    (inputTape x).left.getD i M.machine.blank =
      decodeLeftCell M x t sigma hSat 0 (by omega) i hi := by
  apply decodeLeftCell_unique M x t sigma hSat 0 (by omega) i hi
  have hExact := ntmInitial_left_exact M x t sigma hSat i hi
    ((inputTape x).left.getD i M.machine.blank)
  simpa using hExact

theorem decodeInitial_rightCell
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    (inputTape x).right.getD i M.machine.blank =
      decodeRightCell M x t sigma hSat 0 (by omega) i hi := by
  apply decodeRightCell_unique M x t sigma hSat 0 (by omega) i hi
  have hExact := ntmInitial_right_exact M x t sigma hSat i hi
    ((inputTape x).right.getD i M.machine.blank)
  simpa using hExact

theorem operationalDecodeAgrees_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    OperationalDecodeAgreesAt M x t sigma hSat 0 (by omega) := by
  refine { hState := ?_, hHead := ?_, hLeft := ?_, hRight := ?_ }
  · simpa [operationalDecodeConfig, initialNTMConfig] using
      decodeInitial_state M x t sigma hSat
  · simpa [operationalDecodeConfig, initialNTMConfig] using
      decodeInitial_head M x t sigma hSat
  · intro i hi
    simpa [operationalDecodeConfig, initialNTMConfig] using
      decodeInitial_leftCell M x t sigma hSat i hi
  · intro i hi
    simpa [operationalDecodeConfig, initialNTMConfig] using
      decodeInitial_rightCell M x t sigma hSat i hi

theorem operationalDecodeAgrees_halted_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hA : OperationalDecodeAgreesAt M x t sigma hSat s (by omega))
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hqdec : q = decodeState M x t sigma hSat s (by omega))
    (hadec : a = decodeHead M x t sigma hSat s (by omega))
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    OperationalDecodeAgreesAt M x t sigma hSat (s + 1) (by omega) := by
  subst q
  subst a
  have hq := decodeState_true M x t sigma hSat s (by omega)
  have ha := decodeHead_true M x t sigma hSat s (by omega)
  refine { hState := ?_, hHead := ?_, hLeft := ?_, hRight := ?_ }
  · have hExact := ntmHalted_state_exact M x t s
      (decodeState M x t sigma hSat s (by omega))
      (decodeHead M x t sigma hSat s (by omega))
      sigma hSat hs hq ha hHalt
    have hnext :
        decodeState M x t sigma hSat (s + 1) (by omega) =
          decodeState M x t sigma hSat s (by omega) := by
      apply decodeState_unique M x t sigma hSat (s + 1) (by omega)
      have h := hExact (decodeState M x t sigma hSat s (by omega))
      simpa using h
    simpa [operationalDecodeConfig, hHalt, hnext] using hA.hState
  · have hcopy := ntmHalted_head_copy M x t s
      (decodeState M x t sigma hSat s (by omega))
      (decodeHead M x t sigma hSat s (by omega))
      sigma hSat hs hq ha hHalt
    have hnext :
        decodeHead M x t sigma hSat (s + 1) (by omega) =
          decodeHead M x t sigma hSat s (by omega) := by
      apply decodeHead_unique M x t sigma hSat (s + 1) (by omega)
      have hold := decodeHead_true M x t sigma hSat s (by omega)
      have hn :
          sigma (ntmHeadVar M t (s + 1)
            (decodeHead M x t sigma hSat s (by omega))) = true := by
        rw [hcopy]
        exact hold
      exact hn
    simpa [operationalDecodeConfig, hHalt, hnext] using hA.hHead
  · intro i hi
    have hcopy := ntmHalted_left_copy M x t s
      (decodeState M x t sigma hSat s (by omega))
      (decodeHead M x t sigma hSat s (by omega))
      sigma hSat hs hq ha hHalt i hi
    have hnext :
        decodeLeftCell M x t sigma hSat (s + 1) (by omega) i hi =
          decodeLeftCell M x t sigma hSat s (by omega) i hi := by
      apply decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega) i hi
      have hold := decodeLeftCell_true M x t sigma hSat s (by omega) i hi
      have hn :
          sigma (ntmLeftVar M x t (s + 1) i
            (decodeLeftCell M x t sigma hSat s (by omega) i hi)) = true := by
        rw [hcopy]
        exact hold
      exact hn
    simpa [operationalDecodeConfig, hHalt, hnext] using hA.hLeft i hi
  · intro i hi
    have hcopy := ntmHalted_right_copy M x t s
      (decodeState M x t sigma hSat s (by omega))
      (decodeHead M x t sigma hSat s (by omega))
      sigma hSat hs hq ha hHalt i hi
    have hnext :
        decodeRightCell M x t sigma hSat (s + 1) (by omega) i hi =
          decodeRightCell M x t sigma hSat s (by omega) i hi := by
      apply decodeRightCell_unique M x t sigma hSat (s + 1) (by omega) i hi
      have hold := decodeRightCell_true M x t sigma hSat s (by omega) i hi
      have hn :
          sigma (ntmRightVar M x t (s + 1) i
            (decodeRightCell M x t sigma hSat s (by omega) i hi)) = true := by
        rw [hcopy]
        exact hold
      exact hn
    simpa [operationalDecodeConfig, hHalt, hnext] using hA.hRight i hi


structure OperationalTapeBoundAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (s : Nat) (hs : s <= t) : Prop where
  left_len :
    (operationalDecodeConfig M x t sigma hSat s hs).tape.left.length <= x.length + s
  right_len :
    (operationalDecodeConfig M x t sigma hSat s hs).tape.right.length <= x.length + s

theorem operationalTapeBound_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    OperationalTapeBoundAt M x t sigma hSat 0 (by omega) := by
  refine { left_len := ?_, right_len := ?_ }
  · cases x <;> simp [operationalDecodeConfig, initialNTMConfig, inputTape]
  · cases x <;> simp [operationalDecodeConfig, initialNTMConfig, inputTape]

theorem tapeMove_left_lengths
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.left (tape.write write)).left.length <= tape.left.length ∧
    (Tape.move blank Direction.left (tape.write write)).right.length <= tape.right.length + 1 := by
  cases tape with
  | mk left head right =>
      cases left <;> simp [Tape.write, Tape.move]

theorem tapeMove_right_lengths
    (blank write : Option Bool) (tape : Tape (Option Bool)) :
    (Tape.move blank Direction.right (tape.write write)).left.length <= tape.left.length + 1 ∧
    (Tape.move blank Direction.right (tape.write write)).right.length <= tape.right.length := by
  cases tape with
  | mk left head right =>
      cases right <;> simp [Tape.write, Tape.move]

theorem operationalTapeBound_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hB : OperationalTapeBoundAt M x t sigma hSat s (by omega)) :
    OperationalTapeBoundAt M x t sigma hSat (s + 1) (by omega) := by
  let q := decodeState M x t sigma hSat s (by omega)
  let a := decodeHead M x t sigma hSat s (by omega)
  by_cases hHalt :
      M.machine.accepting q = true ∨ M.machine.rejecting q = true
  · refine { left_len := ?_, right_len := ?_ }
    · simpa [operationalDecodeConfig, q, a, hHalt] using
        Nat.le_trans hB.left_len (by omega : x.length + s <= x.length + (s + 1))
    · simpa [operationalDecodeConfig, q, a, hHalt] using
        Nat.le_trans hB.right_len (by omega : x.length + s <= x.length + (s + 1))
  · have hActive :
        M.machine.accepting q = false ∧ M.machine.rejecting q = false := by
      constructor
      · cases h : M.machine.accepting q with
        | false => rfl
        | true => exact False.elim (hHalt (Or.inl h))
      · cases h : M.machine.rejecting q with
        | false => rfl
        | true => exact False.elim (hHalt (Or.inr h))
    let hq := decodeState_true M x t sigma hSat s (by omega)
    let ha := decodeHead_true M x t sigma hSat s (by omega)
    let j := decodeChoiceIndex M x t s sigma hSat hs q a hq ha hActive
    rcases htr : (M.machine.transition q a).get j with ⟨qNext, write, d⟩
    cases d with
    | stay =>
        refine { left_len := ?_, right_len := ?_ }
        · simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j,
            htr, Tape.write, Tape.move] using
            Nat.le_trans hB.left_len (by omega : x.length + s <= x.length + (s + 1))
        · simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j,
            htr, Tape.write, Tape.move] using
            Nat.le_trans hB.right_len (by omega : x.length + s <= x.length + (s + 1))
    | left =>
        have hlr := tapeMove_left_lengths M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
        refine { left_len := ?_, right_len := ?_ }
        · have := Nat.le_trans hlr.1 hB.left_len
          simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j, htr] using
            Nat.le_trans this (by omega : x.length + s <= x.length + (s + 1))
        · have := Nat.le_trans hlr.2 (Nat.add_le_add_right hB.right_len 1)
          simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j, htr,
            Nat.add_assoc] using this
    | right =>
        have hlr := tapeMove_right_lengths M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
        refine { left_len := ?_, right_len := ?_ }
        · have := Nat.le_trans hlr.1 (Nat.add_le_add_right hB.left_len 1)
          simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j, htr,
            Nat.add_assoc] using this
        · have := Nat.le_trans hlr.2 hB.right_len
          simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j, htr] using
            Nat.le_trans this (by omega : x.length + s <= x.length + (s + 1))

theorem operationalTapeBound_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    ∀ (s : Nat) (hs : s <= t),
      OperationalTapeBoundAt M x t sigma hSat s hs := by
  intro s hs
  induction s with
  | zero =>
      simpa using operationalTapeBound_zero M x t sigma hSat
  | succ s ih =>
      exact operationalTapeBound_step M x t s sigma hSat (by omega) (ih (by omega))

theorem operational_left_getD_outside
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s <= t)
    (hi : x.length + s <= i) :
    (operationalDecodeConfig M x t sigma hSat s hs).tape.left.getD i M.machine.blank =
      M.machine.blank := by
  apply list_getD_eq_default_of_length_le
  exact Nat.le_trans (operationalTapeBound_all M x t sigma hSat s hs).left_len hi

theorem operational_right_getD_outside
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s <= t)
    (hi : x.length + s <= i) :
    (operationalDecodeConfig M x t sigma hSat s hs).tape.right.getD i M.machine.blank =
      M.machine.blank := by
  apply list_getD_eq_default_of_length_le
  exact Nat.le_trans (operationalTapeBound_all M x t sigma hSat s hs).right_len hi


theorem operationalDecodeAgrees_active_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hA : OperationalDecodeAgreesAt M x t sigma hSat s (by omega))
    (hActive :
      M.machine.accepting (decodeState M x t sigma hSat s (by omega)) = false ∧
      M.machine.rejecting (decodeState M x t sigma hSat s (by omega)) = false) :
    OperationalDecodeAgreesAt M x t sigma hSat (s + 1) (by omega) := by
  let q := decodeState M x t sigma hSat s (by omega)
  let a := decodeHead M x t sigma hSat s (by omega)
  let hq := decodeState_true M x t sigma hSat s (by omega)
  let ha := decodeHead_true M x t sigma hSat s (by omega)
  let j := decodeChoiceIndex M x t s sigma hSat hs q a hq ha (by simpa [q] using hActive)
  have hj :
      sigma (ntmChoiceVar M x t s q a j.val) = true := by
    exact decodeChoiceIndex_true M x t s sigma hSat hs q a hq ha
      (by simpa [q] using hActive)
  have hnotHalt :
      ¬ (M.machine.accepting q = true ∨ M.machine.rejecting q = true) := by
    intro h
    rcases h with hacc | hrej
    · have := (by simpa [q] using hActive.1)
      simp [hacc] at this
    · have := (by simpa [q] using hActive.2)
      simp [hrej] at this
  rcases htr : (M.machine.transition q a).get j with ⟨qNext, write, d⟩
  have hStateNext :
      decodeState M x t sigma hSat (s + 1) (by omega) = qNext := by
    simpa [htr] using
      decodeState_choice M x t s sigma hSat hs q a j
        (by simpa [q] using hActive) hj
  cases d with
  | stay =>
      have hHeadNext :
          decodeHead M x t sigma hSat (s + 1) (by omega) = write := by
        simpa [htr] using
          decodeHead_stay M x t s sigma hSat hs q a j
            (by simpa [q] using hActive) hj (by simpa [htr])
      refine { hState := ?_, hHead := ?_, hLeft := ?_, hRight := ?_ }
      · simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hStateNext]
      · have hop := tapeMove_stay_head M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
        simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hHeadNext] using hop
      · intro i hi
        have hop := tapeMove_stay_left_getD M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape i
        have hcell := ntmStay_left_copy_exact M x t s q a j sigma hSat hs
          (by simpa [q] using hActive) hj (by simpa [htr]) i hi
        have hOld := hA.hLeft i hi
        have hNew :
            decodeLeftCell M x t sigma hSat (s + 1) (by omega) i hi =
              decodeLeftCell M x t sigma hSat s (by omega) i hi := by
          apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
            i hi _)
          have hold := decodeLeftCell_true M x t sigma hSat s (by omega) i hi
          have hn :
              sigma (ntmLeftVar M x t (s + 1) i
                (decodeLeftCell M x t sigma hSat s (by omega) i hi)) = true := by
            rw [hcell]
            exact hold
          exact hn
        simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hOld, hNew] using hop
      · intro i hi
        have hop := tapeMove_stay_right_getD M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape i
        have hcell := ntmStay_right_copy_exact M x t s q a j sigma hSat hs
          (by simpa [q] using hActive) hj (by simpa [htr]) i hi
        have hOld := hA.hRight i hi
        have hNew :
            decodeRightCell M x t sigma hSat (s + 1) (by omega) i hi =
              decodeRightCell M x t sigma hSat s (by omega) i hi := by
          apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
            i hi _)
          have hold := decodeRightCell_true M x t sigma hSat s (by omega) i hi
          have hn :
              sigma (ntmRightVar M x t (s + 1) i
                (decodeRightCell M x t sigma hSat s (by omega) i hi)) = true := by
            rw [hcell]
            exact hold
          exact hn
        simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hOld, hNew] using hop
  | left =>
      refine { hState := ?_, hHead := ?_, hLeft := ?_, hRight := ?_ }
      · simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hStateNext]
      · have hop := tapeMove_left_head M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
        have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
        have hOld := hA.hLeft 0 hrpos
        have hHeadCell := ntmChoice_effect_head_exact_left M x t s q a j sigma
          hSat hs (by simpa [q] using hActive) (by simpa [htr]) hj
        have hNext :
            decodeHead M x t sigma hSat (s + 1) (by omega) =
              decodeLeftCell M x t sigma hSat s (by omega) 0 hrpos := by
          apply (decodeHead_unique M x t sigma hSat (s + 1) (by omega) _)
          have hold := decodeLeftCell_true M x t sigma hSat s (by omega) 0 hrpos
          have hn :
              sigma (ntmHeadVar M t (s + 1)
                (decodeLeftCell M x t sigma hSat s (by omega) 0 hrpos)) = true := by
            rw [hHeadCell]
            exact hold
          exact hn
        simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hOld, hNext] using hop
      · intro i hi
        have hop := tapeMove_left_left_getD M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape i
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hout := operational_left_getD_outside M x t s (ntmRadius x t)
            sigma hSat (by omega) (by simp [ntmRadius]; omega)
          have hExact := ntmLeft_blankLeft_exact M x t s q a j sigma hSat hs
            (by simpa [q] using hActive) hj (by simpa [htr])
          have hNext :
              decodeLeftCell M x t sigma hSat (s + 1) (by omega)
                (ntmRadius x t - 1) (by omega) = M.machine.blank := by
            apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
              (ntmRadius x t - 1) (by omega) M.machine.blank)
            simpa using hExact M.machine.blank
          simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
            NTM.stepBranch, hNext, Nat.sub_add_cancel (by simp [ntmRadius] : 1 <= ntmRadius x t)] using
              (hop.trans hout)
        · have hiShift : i < ntmRadius x t - 1 := by omega
          have hiOld : i + 1 < ntmRadius x t := by omega
          have hOld := hA.hLeft (i + 1) hiOld
          have hcell := ntmLeft_shiftedLeft_exact M x t s q a j sigma hSat hs
            (by simpa [q] using hActive) hj (by simpa [htr]) i hiShift
          have hNext :
              decodeLeftCell M x t sigma hSat (s + 1) (by omega) i hi =
                decodeLeftCell M x t sigma hSat s (by omega) (i + 1) hiOld := by
            apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega) i hi _)
            have hold := decodeLeftCell_true M x t sigma hSat s (by omega) (i + 1) hiOld
            have hn :
                sigma (ntmLeftVar M x t (s + 1) i
                  (decodeLeftCell M x t sigma hSat s (by omega) (i + 1) hiOld)) = true := by
              rw [hcell]
              exact hold
            exact hn
          simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
            NTM.stepBranch, hOld, hNext] using hop
      · intro i hi
        cases i with
        | zero =>
            have hop := tapeMove_left_right_zero M.machine.blank write
              (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
            have hExact := ntmLeft_writeRight0_exact M x t s q a j sigma hSat hs
              (by simpa [q] using hActive) hj (by simpa [htr])
            have hNext :
                decodeRightCell M x t sigma hSat (s + 1) (by omega) 0 (by omega) = write := by
              apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
                0 (by omega) write)
              simpa [htr] using hExact write
            simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
              NTM.stepBranch, hNext] using hop
        | succ k =>
            have hk : k < ntmRadius x t - 1 := by omega
            have hkOld : k < ntmRadius x t := by omega
            have hop := tapeMove_left_right_succ M.machine.blank write
              (operationalDecodeConfig M x t sigma hSat s (by omega)).tape k
            have hOld := hA.hRight k hkOld
            have hcell := ntmLeft_shiftedRight_exact M x t s q a j sigma hSat hs
              (by simpa [q] using hActive) hj (by simpa [htr]) k hk
            have hNext :
                decodeRightCell M x t sigma hSat (s + 1) (by omega) (k + 1) hi =
                  decodeRightCell M x t sigma hSat s (by omega) k hkOld := by
              apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
                (k + 1) hi _)
              have hold := decodeRightCell_true M x t sigma hSat s (by omega) k hkOld
              have hn :
                  sigma (ntmRightVar M x t (s + 1) (k + 1)
                    (decodeRightCell M x t sigma hSat s (by omega) k hkOld)) = true := by
                rw [hcell]
                exact hold
              exact hn
            simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
              NTM.stepBranch, hOld, hNext] using hop
  | right =>
      refine { hState := ?_, hHead := ?_, hLeft := ?_, hRight := ?_ }
      · simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hStateNext]
      · have hop := tapeMove_right_head M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
        have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
        have hOld := hA.hRight 0 hrpos
        have hHeadCell := ntmChoice_effect_head_exact_right M x t s q a j sigma
          hSat hs (by simpa [q] using hActive) (by simpa [htr]) hj
        have hNext :
            decodeHead M x t sigma hSat (s + 1) (by omega) =
              decodeRightCell M x t sigma hSat s (by omega) 0 hrpos := by
          apply (decodeHead_unique M x t sigma hSat (s + 1) (by omega) _)
          have hold := decodeRightCell_true M x t sigma hSat s (by omega) 0 hrpos
          have hn :
              sigma (ntmHeadVar M t (s + 1)
                (decodeRightCell M x t sigma hSat s (by omega) 0 hrpos)) = true := by
            rw [hHeadCell]
            exact hold
          exact hn
        simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
          NTM.stepBranch, hOld, hNext] using hop
      · intro i hi
        cases i with
        | zero =>
            have hop := tapeMove_right_left_zero M.machine.blank write
              (operationalDecodeConfig M x t sigma hSat s (by omega)).tape
            have hExact := ntmRight_writeLeft0_exact M x t s q a j sigma hSat hs
              (by simpa [q] using hActive) hj (by simpa [htr])
            have hNext :
                decodeLeftCell M x t sigma hSat (s + 1) (by omega) 0 (by omega) = write := by
              apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
                0 (by omega) write)
              simpa [htr] using hExact write
            simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
              NTM.stepBranch, hNext] using hop
        | succ k =>
            have hk : k < ntmRadius x t - 1 := by omega
            have hkOld : k < ntmRadius x t := by omega
            have hop := tapeMove_right_left_succ M.machine.blank write
              (operationalDecodeConfig M x t sigma hSat s (by omega)).tape k
            have hOld := hA.hLeft k hkOld
            have hcell := ntmRight_shiftedLeft_exact M x t s q a j sigma hSat hs
              (by simpa [q] using hActive) hj (by simpa [htr]) k hk
            have hNext :
                decodeLeftCell M x t sigma hSat (s + 1) (by omega) (k + 1) hi =
                  decodeLeftCell M x t sigma hSat s (by omega) k hkOld := by
              apply (decodeLeftCell_unique M x t sigma hSat (s + 1) (by omega)
                (k + 1) hi _)
              have hold := decodeLeftCell_true M x t sigma hSat s (by omega) k hkOld
              have hn :
                  sigma (ntmLeftVar M x t (s + 1) (k + 1)
                    (decodeLeftCell M x t sigma hSat s (by omega) k hkOld)) = true := by
                rw [hcell]
                exact hold
              exact hn
            simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
              NTM.stepBranch, hOld, hNext] using hop
      · intro i hi
        have hop := tapeMove_right_right_getD M.machine.blank write
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape i
        by_cases hlast : i = ntmRadius x t - 1
        · subst i
          have hout := operational_right_getD_outside M x t s (ntmRadius x t)
            sigma hSat (by omega) (by simp [ntmRadius]; omega)
          have hExact := ntmRight_blankRight_exact M x t s q a j sigma hSat hs
            (by simpa [q] using hActive) hj (by simpa [htr])
          have hNext :
              decodeRightCell M x t sigma hSat (s + 1) (by omega)
                (ntmRadius x t - 1) (by omega) = M.machine.blank := by
            apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega)
              (ntmRadius x t - 1) (by omega) M.machine.blank)
            simpa using hExact M.machine.blank
          simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
            NTM.stepBranch, hNext, Nat.sub_add_cancel (by simp [ntmRadius] : 1 <= ntmRadius x t)] using
              (hop.trans hout)
        · have hiShift : i < ntmRadius x t - 1 := by omega
          have hiOld : i + 1 < ntmRadius x t := by omega
          have hOld := hA.hRight (i + 1) hiOld
          have hcell := ntmRight_shiftedRight_exact M x t s q a j sigma hSat hs
            (by simpa [q] using hActive) hj (by simpa [htr]) i hiShift
          have hNext :
              decodeRightCell M x t sigma hSat (s + 1) (by omega) i hi =
                decodeRightCell M x t sigma hSat s (by omega) (i + 1) hiOld := by
            apply (decodeRightCell_unique M x t sigma hSat (s + 1) (by omega) i hi _)
            have hold := decodeRightCell_true M x t sigma hSat s (by omega) (i + 1) hiOld
            have hn :
                sigma (ntmRightVar M x t (s + 1) i
                  (decodeRightCell M x t sigma hSat s (by omega) (i + 1) hiOld)) = true := by
              rw [hcell]
              exact hold
            exact hn
          simpa [operationalDecodeConfig, q, a, hnotHalt, hActive, hq, ha, j, htr,
            NTM.stepBranch, hOld, hNext] using hop

theorem operationalDecodeAgrees_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall s : Nat, s <= t ->
      OperationalDecodeAgreesAt M x t sigma hSat s (by assumption) := by
  intro s
  induction s with
  | zero =>
      intro _
      simpa using operationalDecodeAgrees_zero M x t sigma hSat
  | succ s ih =>
      intro hsle
      have hslt : s < t := by omega
      have hA := ih (by omega)
      let q := decodeState M x t sigma hSat s (by omega)
      by_cases hHalt :
          M.machine.accepting q = true ∨ M.machine.rejecting q = true
      · exact operationalDecodeAgrees_halted_step M x t s sigma hSat hslt hA
          q (decodeHead M x t sigma hSat s (by omega)) rfl rfl hHalt
      · have hActive :
            M.machine.accepting q = false ∧ M.machine.rejecting q = false := by
          constructor
          · cases h : M.machine.accepting q with
            | false => rfl
            | true => exact False.elim (hHalt (Or.inl h))
          · cases h : M.machine.rejecting q with
            | false => rfl
            | true => exact False.elim (hHalt (Or.inr h))
        exact operationalDecodeAgrees_active_step M x t s sigma hSat hslt hA
          (by simpa [q] using hActive)


theorem ntmDecode_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t) :
    NTMTableauStep M
      (operationalDecodeConfig M x t sigma hSat s (by omega))
      (operationalDecodeConfig M x t sigma hSat (s + 1) (by omega)) := by
  let q := decodeState M x t sigma hSat s (by omega)
  let a := decodeHead M x t sigma hSat s (by omega)
  have hA := operationalDecodeAgrees_all M x t sigma hSat s (by omega)
  by_cases hHalt :
      M.machine.accepting q = true ∨ M.machine.rejecting q = true
  · left
    constructor
    · simpa [NTMHalted, hA.hState, q] using hHalt
    · simp [operationalDecodeConfig, q, a, hHalt]
  · have hActive :
        M.machine.accepting q = false ∧ M.machine.rejecting q = false := by
      constructor
      · cases h : M.machine.accepting q with
        | false => rfl
        | true => exact False.elim (hHalt (Or.inl h))
      · cases h : M.machine.rejecting q with
        | false => rfl
        | true => exact False.elim (hHalt (Or.inr h))
    let hq := decodeState_true M x t sigma hSat s (by omega)
    let ha := decodeHead_true M x t sigma hSat s (by omega)
    let j := decodeChoiceIndex M x t s sigma hSat hs q a hq ha hActive
    let tr := (M.machine.transition q a).get j
    right
    constructor
    · intro hh
      have hh' :
          M.machine.accepting q = true ∨ M.machine.rejecting q = true := by
        simpa [NTMHalted, hA.hState, q] using hh
      exact hHalt hh'
    · have htrmem : tr ∈ M.machine.transition q a := by
        dsimp [tr]
        exact List.get_mem _ _
      have hstates :
          (operationalDecodeConfig M x t sigma hSat s (by omega)).state = q := by
        simpa [q] using hA.hState
      have hheads :
          (operationalDecodeConfig M x t sigma hSat s (by omega)).tape.head = a := by
        simpa [a] using hA.hHead
      have hsucc :
          M.machine.stepBranch
              (operationalDecodeConfig M x t sigma hSat s (by omega)) tr
            ∈
          M.machine.successors
              (operationalDecodeConfig M x t sigma hSat s (by omega)) := by
        simp [NTM.successors, hstates, hheads, htrmem]
      simpa [operationalDecodeConfig, q, a, hHalt, hActive, hq, ha, j, tr] using hsucc


noncomputable def operationalPath
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Fin (t + 1)) : NTMConfig M :=
  operationalDecodeConfig M x t sigma hSat i.val (by omega)

theorem operationalPath_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    operationalPath M x t sigma hSat 0 =
      initialNTMConfig M.machine x := by
  simp [operationalPath, operationalDecodeConfig]

theorem operationalPath_step
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Fin t) :
    NTMTableauStep M
      (operationalPath M x t sigma hSat i.castSucc)
      (operationalPath M x t sigma hSat i.succ) := by
  simpa [operationalPath] using
    ntmDecode_step M x t i.val sigma hSat i.isLt

theorem operationalPath_is_tableauPath
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    NTMTableauPath M t (initialNTMConfig M.machine x)
      (operationalPath M x t sigma hSat) := by
  constructor
  · exact operationalPath_zero M x t sigma hSat
  · intro i
    exact operationalPath_step M x t sigma hSat i

theorem boundedExec_final_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    evalNTMCNF sigma (ntmFinalAcceptanceCNF M t) = true := by
  have hAll :=
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)).mp
      (by simpa [boundedExecTableauCNF_NTM, List.append_assoc] using hSat)
  exact (evalNTMCNF_append sigma
    (ntmTransitionsCNF M x t)
    (ntmFinalAcceptanceCNF M t)).mp hAll.2 |>.2

theorem acceptingStateLits_sat_exists
    (M : PolyNTMCandidate) (t : Nat) (sigma : Assignment)
    (h :
      evalNTMClause sigma (ntmAcceptingStateLits M t) = true) :
    ∃ q : Fin (M.stateCount + 1),
      M.machine.accepting q = true ∧
      sigma (ntmStateVar M t t q) = true := by
  unfold ntmAcceptingStateLits at h
  let qs := List.ofFn (fun q : Fin (M.stateCount + 1) => q)
  induction qs with
  | nil =>
      simp [evalNTMClause] at h
  | cons q qs ih =>
      by_cases hacc : M.machine.accepting q = true
      · simp [List.filterMap_cons, hacc, evalNTMClause, evalNTMLiteral, ntmPos,
          Bool.or_eq_true] at h
        rcases h with hq | hrest
        · exact ⟨q, hacc, hq⟩
        · rcases ih hrest with ⟨r, hracc, hrsig⟩
          exact ⟨r, hracc, hrsig⟩
      · have haccf : M.machine.accepting q = false := by
          cases hq : M.machine.accepting q <;> simp_all
        simp [List.filterMap_cons, haccf] at h
        exact ih h

theorem decode_accepting
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    M.machine.accepting
      (decodeState M x t sigma hSat t (by omega)) = true := by
  have hFinal := boundedExec_final_sat M x t sigma hSat
  have hClause :
      evalNTMClause sigma (ntmAcceptingStateLits M t) = true := by
    simpa [ntmFinalAcceptanceCNF, evalNTMCNF] using hFinal
  rcases acceptingStateLits_sat_exists M t sigma hClause with
    ⟨q, hqacc, hqtrue⟩
  have hqeq := decodeState_unique M x t sigma hSat t (by omega) q hqtrue
  simpa [hqeq] using hqacc

theorem operationalPath_accepting
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    M.machine.accepting
      (operationalPath M x t sigma hSat (Fin.last t)).state = true := by
  have hA := operationalDecodeAgrees_all M x t sigma hSat t (by omega)
  have hacc := decode_accepting M x t sigma hSat
  simpa [operationalPath, hA.hState] using hacc

theorem operationalTableauAcceptingPath
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    NTMTableauAcceptingPath M t (initialNTMConfig M.machine x) := by
  refine ⟨operationalPath M x t sigma hSat, ?_, ?_⟩
  · exact operationalPath_is_tableauPath M x t sigma hSat
  · exact operationalPath_accepting M x t sigma hSat

theorem tableau_soundness_from_assignment
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    M.machine.AcceptsWithin t (initialNTMConfig M.machine x) := by
  exact path_to_acceptsWithin M t (initialNTMConfig M.machine x)
    (operationalTableauAcceptingPath M x t sigma hSat)


theorem ntmSymbolCode_lt_three
    (a : Option Bool) :
    ntmSymbolCode a < 3 := by
  cases a <;> simp [ntmSymbolCode]

theorem ntmStateVar_lt_headBase
    (M : PolyNTMCandidate) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (hs : s <= t) :
    ntmStateVar M t s q < ntmHeadBase M t := by
  simp [ntmStateVar, ntmHeadBase, ntmStateSlots, ntmStateCount]
  have hq := q.isLt
  omega

theorem ntmHeadVar_range
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (a : Option Bool)
    (hs : s <= t) :
    ntmHeadBase M t <= ntmHeadVar M t s a ∧
      ntmHeadVar M t s a < ntmLeftBase M x t := by
  constructor
  · simp [ntmHeadVar]
  · simp [ntmHeadVar, ntmLeftBase]
    have ha := ntmSymbolCode_lt_three a
    omega

theorem ntmLeftVar_range
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool)
    (hs : s <= t) (hi : i < ntmRadius x t) :
    ntmLeftBase M x t <= ntmLeftVar M x t s i a ∧
      ntmLeftVar M x t s i a < ntmRightBase M x t := by
  constructor
  · simp [ntmLeftVar]
  · simp [ntmLeftVar, ntmRightBase]
    have ha := ntmSymbolCode_lt_three a
    omega

theorem ntmRightVar_range
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool)
    (hs : s <= t) (hi : i < ntmRadius x t) :
    ntmRightBase M x t <= ntmRightVar M x t s i a ∧
      ntmRightVar M x t s i a < ntmChoiceBase M x t := by
  constructor
  · simp [ntmRightVar]
  · simp [ntmRightVar, ntmChoiceBase]
    have ha := ntmSymbolCode_lt_three a
    omega

theorem stateVar_ne_headVar
    (M : PolyNTMCandidate) (x : BitString) (t s1 s2 : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs1 : s1 <= t) (hs2 : s2 <= t) :
    ntmStateVar M t s1 q ≠ ntmHeadVar M t s2 a := by
  have h1 := ntmStateVar_lt_headBase M t s1 q hs1
  have h2 := (ntmHeadVar_range M x t s2 a hs2).1
  omega

theorem headVar_ne_leftVar
    (M : PolyNTMCandidate) (x : BitString) (t s1 s2 i : Nat)
    (a b : Option Bool)
    (hs1 : s1 <= t) (hs2 : s2 <= t) (hi : i < ntmRadius x t) :
    ntmHeadVar M t s1 a ≠ ntmLeftVar M x t s2 i b := by
  have h1 := (ntmHeadVar_range M x t s1 a hs1).2
  have h2 := (ntmLeftVar_range M x t s2 i b hs2 hi).1
  omega

theorem leftVar_ne_rightVar
    (M : PolyNTMCandidate) (x : BitString) (t s1 s2 i j : Nat)
    (a b : Option Bool)
    (hs1 : s1 <= t) (hs2 : s2 <= t)
    (hi : i < ntmRadius x t) (hj : j < ntmRadius x t) :
    ntmLeftVar M x t s1 i a ≠ ntmRightVar M x t s2 j b := by
  have h1 := (ntmLeftVar_range M x t s1 i a hs1 hi).2
  have h2 := (ntmRightVar_range M x t s2 j b hs2 hj).1
  omega

theorem rightVar_lt_choiceBase
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool)
    (hs : s <= t) (hi : i < ntmRadius x t) :
    ntmRightVar M x t s i a < ntmChoiceBase M x t :=
  (ntmRightVar_range M x t s i a hs hi).2


theorem transition_mem_to_idx
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (tr : State × Symbol × Direction)
    (hmem : tr ∈ ts) :
    ∃ j : Nat, ∃ hj : j < ts.length, ts.get ⟨j, hj⟩ = tr := by
  induction ts with
  | nil =>
      simp at hmem
  | cons x xs ih =>
      simp at hmem
      rcases hmem with rfl | hmem
      · exact ⟨0, by simp, by simp⟩
      · rcases ih hmem with ⟨j, hj, hget⟩
        exact ⟨j + 1, by simp [hj], by simpa using hget⟩

theorem active_step_transition_witness
    (M : PolyNTMCandidate)
    (c c' : NTMConfig M)
    (hStep : NTMTableauStep M c c')
    (hActive : NTMActive M c) :
    ∃ tr ∈ M.machine.transition c.state c.tape.head,
      c' = M.machine.stepBranch c tr := by
  rcases hStep with hhalt | hactive
  · exact False.elim (hActive hhalt.1)
  · rcases hactive with ⟨_, hsucc⟩
    simp [NTM.successors] at hsucc
    rcases hsucc with ⟨tr, hmem, rfl⟩
    exact ⟨tr, hmem, rfl⟩

noncomputable def choiceIdxOfStep
    (M : PolyNTMCandidate)
    (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s < t) : Nat :=
  let c := path ⟨s, by omega⟩
  let c' := path ⟨s + 1, by omega⟩
  if hActive : NTMActive M c then
    let hStep : NTMTableauStep M c c' := by
      simpa [c, c'] using hPath.2 ⟨s, hs⟩
    let tr := (active_step_transition_witness M c c' hStep hActive).choose
    let hmem := (active_step_transition_witness M c c' hStep hActive).choose_spec.1
    (transition_mem_to_idx (M.machine.transition c.state c.tape.head) tr hmem).choose
  else
    0

theorem choiceIdxOfStep_active_spec
    (M : PolyNTMCandidate)
    (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s < t)
    (hActive : NTMActive M (path ⟨s, by omega⟩)) :
    ∃ hj :
        choiceIdxOfStep M t path hPath s hs <
          (M.machine.transition
            (path ⟨s, by omega⟩).state
            (path ⟨s, by omega⟩).tape.head).length,
      (M.machine.transition
        (path ⟨s, by omega⟩).state
        (path ⟨s, by omega⟩).tape.head).get
          ⟨choiceIdxOfStep M t path hPath s hs, hj⟩
        =
      (active_step_transition_witness M
        (path ⟨s, by omega⟩)
        (path ⟨s + 1, by omega⟩)
        (by simpa using hPath.2 ⟨s, hs⟩)
        hActive).choose := by
  unfold choiceIdxOfStep
  simp [hActive]
  let W := active_step_transition_witness M
    (path ⟨s, by omega⟩)
    (path ⟨s + 1, by omega⟩)
    (by simpa using hPath.2 ⟨s, hs⟩)
    hActive
  rcases transition_mem_to_idx
      (M.machine.transition
        (path ⟨s, by omega⟩).state
        (path ⟨s, by omega⟩).tape.head)
      W.choose W.choose_spec.1 with ⟨j, hj, hget⟩
  exact ⟨hj, hget⟩


theorem foldl_max_ge_acc
    (xs : List Nat) (acc : Nat) :
    acc <= xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left acc x) (ih (Nat.max acc x))

theorem foldl_max_ge_of_mem
    (xs : List Nat) (x acc : Nat)
    (hx : x ∈ xs) :
    x <= xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · exact Nat.le_trans (Nat.le_max_right acc y)
          (foldl_max_ge_acc ys (Nat.max acc y))
      · exact ih hx

theorem foldl_max_le_of_all_le
    (xs : List Nat) (acc cap : Nat)
    (hacc : acc <= cap)
    (hall : forall x, x ∈ xs -> x <= cap) :
    xs.foldl Nat.max acc <= cap := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      apply ih (Nat.max acc x)
      · exact Nat.max_le hacc (hall x (by simp))
      · intro y hy
        exact hall y (by simp [hy])

theorem ntmBranchBound_ge_transition_length
    (M : PolyNTMCandidate)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    (M.machine.transition q a).length <= ntmBranchBound M := by
  unfold ntmBranchBound
  apply foldl_max_ge_of_mem
  simp [ntmAlphabet]

theorem choiceIdxOfStep_lt_branchBound_succ
    (M : PolyNTMCandidate)
    (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s < t)
    (hActive : NTMActive M (path ⟨s, by omega⟩)) :
    choiceIdxOfStep M t path hPath s hs < ntmBranchBound M + 1 := by
  rcases choiceIdxOfStep_active_spec M t path hPath s hs hActive with
    ⟨hj, _⟩
  have hb := ntmBranchBound_ge_transition_length M
    (path ⟨s, by omega⟩).state
    (path ⟨s, by omega⟩).tape.head
  omega

theorem ntmChoiceVar_ge_choiceBase
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) (j : Nat) :
    ntmChoiceBase M x t <= ntmChoiceVar M x t s q a j := by
  simp [ntmChoiceVar]


theorem mul_add_encode_injective
    (stride s k s' k' : Nat)
    (hstride : 0 < stride)
    (hk : k < stride)
    (hk' : k' < stride)
    (hEq : s * stride + k = s' * stride + k') :
    s = s' ∧ k = k' := by
  have hmod := congrArg (fun n => n % stride) hEq
  have hdiv := congrArg (fun n => n / stride) hEq
  have hkmod : (s * stride + k) % stride = k := by
    simp [Nat.add_mod, Nat.mul_mod, hk, Nat.mod_eq_of_lt]
  have hk'mod : (s' * stride + k') % stride = k' := by
    simp [Nat.add_mod, Nat.mul_mod, hk', Nat.mod_eq_of_lt]
  have hkEq : k = k' := by
    simpa [hkmod, hk'mod] using hmod
  subst k'
  have hsdiv : (s * stride + k) / stride = s := by
    calc
      (s * stride + k) / stride = (k + stride * s) / stride := by
        simp [Nat.mul_comm, Nat.add_comm]
      _ = k / stride + s := Nat.add_mul_div_left k s hstride
      _ = s := by simp [Nat.div_eq_of_lt hk]
  have hs'div : (s' * stride + k) / stride = s' := by
    calc
      (s' * stride + k) / stride = (k + stride * s') / stride := by
        simp [Nat.mul_comm, Nat.add_comm]
      _ = k / stride + s' := Nat.add_mul_div_left k s' hstride
      _ = s' := by simp [Nat.div_eq_of_lt hk]
  simpa [hsdiv, hs'div] using hdiv

theorem ntmStateVar_injective
    (M : PolyNTMCandidate) (t s s' : Nat)
    (q q' : Fin (M.stateCount + 1))
    (hEq : ntmStateVar M t s q = ntmStateVar M t s' q') :
    s = s' ∧ q = q' := by
  have hstride : 0 < ntmStateCount M := by
    simp [ntmStateCount]
  have h := mul_add_encode_injective (ntmStateCount M) s q.val s' q'.val
    hstride (by simpa [ntmStateCount] using q.isLt)
    (by simpa [ntmStateCount] using q'.isLt)
    (by simpa [ntmStateVar] using hEq)
  refine ⟨h.1, Fin.ext ?_⟩
  exact h.2

theorem ntmHeadVar_injective
    (M : PolyNTMCandidate) (t s s' : Nat)
    (a a' : Option Bool)
    (hEq : ntmHeadVar M t s a = ntmHeadVar M t s' a') :
    s = s' ∧ a = a' := by
  have hraw :
      s * 3 + ntmSymbolCode a =
        s' * 3 + ntmSymbolCode a' := by
    simpa [ntmHeadVar] using
      Nat.add_left_cancel hEq
  have h := mul_add_encode_injective 3 s (ntmSymbolCode a) s' (ntmSymbolCode a')
    (by decide) (ntmSymbolCode_lt_three a) (ntmSymbolCode_lt_three a') hraw
  refine ⟨h.1, ?_⟩
  cases a <;> cases a' <;> simp_all [ntmSymbolCode]

theorem ntmLeftVar_injective
    (M : PolyNTMCandidate) (x : BitString) (t s s' i i' : Nat)
    (a a' : Option Bool)
    (hi : i < ntmRadius x t)
    (hi' : i' < ntmRadius x t)
    (hEq : ntmLeftVar M x t s i a = ntmLeftVar M x t s' i' a') :
    s = s' ∧ i = i' ∧ a = a' := by
  have hraw :
      (s * ntmRadius x t + i) * 3 + ntmSymbolCode a =
        (s' * ntmRadius x t + i') * 3 + ntmSymbolCode a' := by
    simpa [ntmLeftVar] using Nat.add_left_cancel hEq
  have h1 := mul_add_encode_injective 3
    (s * ntmRadius x t + i) (ntmSymbolCode a)
    (s' * ntmRadius x t + i') (ntmSymbolCode a')
    (by decide) (ntmSymbolCode_lt_three a) (ntmSymbolCode_lt_three a') hraw
  have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
  have h2 := mul_add_encode_injective (ntmRadius x t)
    s i s' i' hrpos hi hi' h1.1
  refine ⟨h2.1, h2.2, ?_⟩
  cases a <;> cases a' <;> simp_all [ntmSymbolCode]

theorem ntmRightVar_injective
    (M : PolyNTMCandidate) (x : BitString) (t s s' i i' : Nat)
    (a a' : Option Bool)
    (hi : i < ntmRadius x t)
    (hi' : i' < ntmRadius x t)
    (hEq : ntmRightVar M x t s i a = ntmRightVar M x t s' i' a') :
    s = s' ∧ i = i' ∧ a = a' := by
  have hraw :
      (s * ntmRadius x t + i) * 3 + ntmSymbolCode a =
        (s' * ntmRadius x t + i') * 3 + ntmSymbolCode a' := by
    simpa [ntmRightVar] using Nat.add_left_cancel hEq
  have h1 := mul_add_encode_injective 3
    (s * ntmRadius x t + i) (ntmSymbolCode a)
    (s' * ntmRadius x t + i') (ntmSymbolCode a')
    (by decide) (ntmSymbolCode_lt_three a) (ntmSymbolCode_lt_three a') hraw
  have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
  have h2 := mul_add_encode_injective (ntmRadius x t)
    s i s' i' hrpos hi hi' h1.1
  refine ⟨h2.1, h2.2, ?_⟩
  cases a <;> cases a' <;> simp_all [ntmSymbolCode]

theorem ntmChoiceVar_injective
    (M : PolyNTMCandidate) (x : BitString) (t s s' : Nat)
    (q q' : Fin (M.stateCount + 1))
    (a a' : Option Bool)
    (j j' : Nat)
    (hj : j < ntmBranchBound M + 1)
    (hj' : j' < ntmBranchBound M + 1)
    (hEq :
      ntmChoiceVar M x t s q a j =
        ntmChoiceVar M x t s' q' a' j') :
    s = s' ∧ q = q' ∧ a = a' ∧ j = j' := by
  have hraw :
      (((s * ntmStateCount M + q.val) * 3 + ntmSymbolCode a) *
          (ntmBranchBound M + 1)) + j =
      (((s' * ntmStateCount M + q'.val) * 3 + ntmSymbolCode a') *
          (ntmBranchBound M + 1)) + j' := by
    simpa [ntmChoiceVar] using Nat.add_left_cancel hEq
  have hstride : 0 < ntmBranchBound M + 1 := by omega
  have h1 := mul_add_encode_injective (ntmBranchBound M + 1)
    ((s * ntmStateCount M + q.val) * 3 + ntmSymbolCode a) j
    ((s' * ntmStateCount M + q'.val) * 3 + ntmSymbolCode a') j'
    hstride hj hj' hraw
  have h2 := mul_add_encode_injective 3
    (s * ntmStateCount M + q.val) (ntmSymbolCode a)
    (s' * ntmStateCount M + q'.val) (ntmSymbolCode a')
    (by decide) (ntmSymbolCode_lt_three a) (ntmSymbolCode_lt_three a') h1.1
  have hstate := mul_add_encode_injective (ntmStateCount M)
    s q.val s' q'.val
    (by simp [ntmStateCount])
    (by simpa [ntmStateCount] using q.isLt)
    (by simpa [ntmStateCount] using q'.isLt)
    h2.1
  refine ⟨hstate.1, Fin.ext hstate.2, ?_, h1.2⟩
  cases a <;> cases a' <;> simp_all [ntmSymbolCode]


def PathAssignmentStateTrue
    (M : PolyNTMCandidate) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (v : Nat) : Prop :=
  ∃ s : Nat, ∃ hs : s <= t,
    v = ntmStateVar M t s (path ⟨s, by omega⟩).state

def PathAssignmentHeadTrue
    (M : PolyNTMCandidate) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (v : Nat) : Prop :=
  ∃ s : Nat, ∃ hs : s <= t,
    v = ntmHeadVar M t s (path ⟨s, by omega⟩).tape.head

def PathAssignmentLeftTrue
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (v : Nat) : Prop :=
  ∃ s : Nat, ∃ hs : s <= t, ∃ i : Nat, ∃ hi : i < ntmRadius x t,
    v = ntmLeftVar M x t s i
      ((path ⟨s, by omega⟩).tape.left.getD i M.machine.blank)

def PathAssignmentRightTrue
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (v : Nat) : Prop :=
  ∃ s : Nat, ∃ hs : s <= t, ∃ i : Nat, ∃ hi : i < ntmRadius x t,
    v = ntmRightVar M x t s i
      ((path ⟨s, by omega⟩).tape.right.getD i M.machine.blank)

def PathAssignmentChoiceTrue
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (v : Nat) : Prop :=
  ∃ s : Nat, ∃ hs : s < t,
    NTMActive M (path ⟨s, by omega⟩) ∧
    v = ntmChoiceVar M x t s
      (path ⟨s, by omega⟩).state
      (path ⟨s, by omega⟩).tape.head
      (choiceIdxOfStep M t path hPath s hs)

noncomputable def pathAssignment
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path) :
    Assignment :=
  fun v =>
    decide (
      PathAssignmentStateTrue M t path v ∨
      PathAssignmentHeadTrue M t path v ∨
      PathAssignmentLeftTrue M x t path v ∨
      PathAssignmentRightTrue M x t path v ∨
      PathAssignmentChoiceTrue M x t path hPath v)

theorem pathAssignment_state
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (q : Fin (M.stateCount + 1)) :
    pathAssignment M x t path hPath (ntmStateVar M t s q) =
      decide (q = (path ⟨s, by omega⟩).state) := by
  by_cases hq : q = (path ⟨s, by omega⟩).state
  · subst q
    simp [pathAssignment, PathAssignmentStateTrue, hs]
  · have hnotState :
        ¬ PathAssignmentStateTrue M t path (ntmStateVar M t s q) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      have hinj := ntmStateVar_injective M t s s' q
        (path ⟨s', by omega⟩).state heq
      exact hq (by simpa [hinj.1] using hinj.2)
    have hnotHead :
        ¬ PathAssignmentHeadTrue M t path (ntmStateVar M t s q) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      exact stateVar_ne_headVar M x t s s' q
        (path ⟨s', by omega⟩).tape.head hs hs' heq
    have hnotLeft :
        ¬ PathAssignmentLeftTrue M x t path (ntmStateVar M t s q) := by
      intro h
      rcases h with ⟨s', hs', i, hi, heq⟩
      have hslt := ntmStateVar_lt_headBase M t s q hs
      have hl := (ntmLeftVar_range M x t s' i
        ((path ⟨s', by omega⟩).tape.left.getD i M.machine.blank) hs' hi).1
      have hb : ntmHeadBase M t <= ntmLeftBase M x t := by
        simp [ntmLeftBase]
      omega
    have hnotRight :
        ¬ PathAssignmentRightTrue M x t path (ntmStateVar M t s q) := by
      intro h
      rcases h with ⟨s', hs', i, hi, heq⟩
      have hslt := ntmStateVar_lt_headBase M t s q hs
      have hr := (ntmRightVar_range M x t s' i
        ((path ⟨s', by omega⟩).tape.right.getD i M.machine.blank) hs' hi).1
      have hb : ntmHeadBase M t <= ntmRightBase M x t := by
        simp [ntmRightBase, ntmLeftBase]
      omega
    have hnotChoice :
        ¬ PathAssignmentChoiceTrue M x t path hPath (ntmStateVar M t s q) := by
      intro h
      rcases h with ⟨s', hs', hactive, heq⟩
      have hslt := ntmStateVar_lt_headBase M t s q hs
      have hc := ntmChoiceVar_ge_choiceBase M x t s'
        (path ⟨s', by omega⟩).state
        (path ⟨s', by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s' hs')
      have hb : ntmHeadBase M t <= ntmChoiceBase M x t := by
        unfold ntmChoiceBase ntmRightBase ntmLeftBase
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      omega
    simp [pathAssignment, hnotState, hnotHead, hnotLeft, hnotRight, hnotChoice, hq]

theorem pathAssignment_head
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (a : Option Bool) :
    pathAssignment M x t path hPath (ntmHeadVar M t s a) =
      decide (a = (path ⟨s, by omega⟩).tape.head) := by
  by_cases ha : a = (path ⟨s, by omega⟩).tape.head
  · subst a
    simp [pathAssignment, PathAssignmentHeadTrue, hs]
  · have hnotState :
        ¬ PathAssignmentStateTrue M t path (ntmHeadVar M t s a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      exact stateVar_ne_headVar M x t s' s
        (path ⟨s', by omega⟩).state a hs' hs heq.symm
    have hnotHead :
        ¬ PathAssignmentHeadTrue M t path (ntmHeadVar M t s a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      have hinj := ntmHeadVar_injective M t s s' a
        (path ⟨s', by omega⟩).tape.head heq
      exact ha (by simpa [hinj.1] using hinj.2)
    have hnotLeft :
        ¬ PathAssignmentLeftTrue M x t path (ntmHeadVar M t s a) := by
      intro h
      rcases h with ⟨s', hs', i, hi, heq⟩
      exact headVar_ne_leftVar M x t s s' i a
        ((path ⟨s', by omega⟩).tape.left.getD i M.machine.blank)
        hs hs' hi heq
    have hnotRight :
        ¬ PathAssignmentRightTrue M x t path (ntmHeadVar M t s a) := by
      intro h
      rcases h with ⟨s', hs', i, hi, heq⟩
      have hh := (ntmHeadVar_range M x t s a hs).2
      have hr := (ntmRightVar_range M x t s' i
        ((path ⟨s', by omega⟩).tape.right.getD i M.machine.blank) hs' hi).1
      have hb : ntmLeftBase M x t <= ntmRightBase M x t := by
        simp [ntmRightBase]
      omega
    have hnotChoice :
        ¬ PathAssignmentChoiceTrue M x t path hPath (ntmHeadVar M t s a) := by
      intro h
      rcases h with ⟨s', hs', hactive, heq⟩
      have hh := (ntmHeadVar_range M x t s a hs).2
      have hc := ntmChoiceVar_ge_choiceBase M x t s'
        (path ⟨s', by omega⟩).state
        (path ⟨s', by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s' hs')
      have hb : ntmLeftBase M x t <= ntmChoiceBase M x t := by
        unfold ntmChoiceBase ntmRightBase
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      omega
    simp [pathAssignment, hnotState, hnotHead, hnotLeft, hnotRight, hnotChoice, ha]


theorem pathAssignment_left
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t)
    (a : Option Bool) :
    pathAssignment M x t path hPath (ntmLeftVar M x t s i a) =
      decide (a = (path ⟨s, by omega⟩).tape.left.getD i M.machine.blank) := by
  by_cases ha : a = (path ⟨s, by omega⟩).tape.left.getD i M.machine.blank
  · subst a
    simp [pathAssignment, PathAssignmentLeftTrue, hs, hi]
  · have hnotLeft :
        ¬ PathAssignmentLeftTrue M x t path (ntmLeftVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', i', hi', heq⟩
      have hinj := ntmLeftVar_injective M x t s s' i i' a
        ((path ⟨s', by omega⟩).tape.left.getD i' M.machine.blank)
        hi hi' heq
      subst s'
      subst i'
      exact ha hinj.2.2
    have hnotState :
        ¬ PathAssignmentStateTrue M t path (ntmLeftVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      have hslt := ntmStateVar_lt_headBase M t s'
        (path ⟨s', by omega⟩).state hs'
      have hl := (ntmLeftVar_range M x t s i a hs hi).1
      have hb : ntmHeadBase M t <= ntmLeftBase M x t := by
        simp [ntmLeftBase]
      omega
    have hnotHead :
        ¬ PathAssignmentHeadTrue M t path (ntmLeftVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      exact headVar_ne_leftVar M x t s' s i
        (path ⟨s', by omega⟩).tape.head a hs' hs hi heq.symm
    have hnotRight :
        ¬ PathAssignmentRightTrue M x t path (ntmLeftVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', i', hi', heq⟩
      exact leftVar_ne_rightVar M x t s s' i i' a
        ((path ⟨s', by omega⟩).tape.right.getD i' M.machine.blank)
        hs hs' hi hi' heq
    have hnotChoice :
        ¬ PathAssignmentChoiceTrue M x t path hPath (ntmLeftVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', hactive, heq⟩
      have hl := (ntmLeftVar_range M x t s i a hs hi).2
      have hc := ntmChoiceVar_ge_choiceBase M x t s'
        (path ⟨s', by omega⟩).state
        (path ⟨s', by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s' hs')
      have hb : ntmRightBase M x t <= ntmChoiceBase M x t := by
        simp [ntmChoiceBase]
      omega
    simp [pathAssignment, hnotState, hnotHead, hnotLeft, hnotRight, hnotChoice, ha]

theorem pathAssignment_right
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (i : Nat) (hi : i < ntmRadius x t)
    (a : Option Bool) :
    pathAssignment M x t path hPath (ntmRightVar M x t s i a) =
      decide (a = (path ⟨s, by omega⟩).tape.right.getD i M.machine.blank) := by
  by_cases ha : a = (path ⟨s, by omega⟩).tape.right.getD i M.machine.blank
  · subst a
    simp [pathAssignment, PathAssignmentRightTrue, hs, hi]
  · have hnotRight :
        ¬ PathAssignmentRightTrue M x t path (ntmRightVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', i', hi', heq⟩
      have hinj := ntmRightVar_injective M x t s s' i i' a
        ((path ⟨s', by omega⟩).tape.right.getD i' M.machine.blank)
        hi hi' heq
      subst s'
      subst i'
      exact ha hinj.2.2
    have hnotState :
        ¬ PathAssignmentStateTrue M t path (ntmRightVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      have hslt := ntmStateVar_lt_headBase M t s'
        (path ⟨s', by omega⟩).state hs'
      have hr := (ntmRightVar_range M x t s i a hs hi).1
      have hb : ntmHeadBase M t <= ntmRightBase M x t := by
        simp [ntmRightBase, ntmLeftBase]
      omega
    have hnotHead :
        ¬ PathAssignmentHeadTrue M t path (ntmRightVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', heq⟩
      have hh := (ntmHeadVar_range M x t s'
        (path ⟨s', by omega⟩).tape.head hs').2
      have hr := (ntmRightVar_range M x t s i a hs hi).1
      have hb : ntmLeftBase M x t <= ntmRightBase M x t := by
        simp [ntmRightBase]
      omega
    have hnotLeft :
        ¬ PathAssignmentLeftTrue M x t path (ntmRightVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', i', hi', heq⟩
      exact leftVar_ne_rightVar M x t s' s i' i
        ((path ⟨s', by omega⟩).tape.left.getD i' M.machine.blank) a
        hs' hs hi' hi heq.symm
    have hnotChoice :
        ¬ PathAssignmentChoiceTrue M x t path hPath (ntmRightVar M x t s i a) := by
      intro h
      rcases h with ⟨s', hs', hactive, heq⟩
      have hr := (ntmRightVar_range M x t s i a hs hi).2
      have hc := ntmChoiceVar_ge_choiceBase M x t s'
        (path ⟨s', by omega⟩).state
        (path ⟨s', by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s' hs')
      omega
    simp [pathAssignment, hnotState, hnotHead, hnotLeft, hnotRight, hnotChoice, ha]

theorem pathAssignment_choice_selected
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s < t)
    (hActive : NTMActive M (path ⟨s, by omega⟩)) :
    pathAssignment M x t path hPath
      (ntmChoiceVar M x t s
        (path ⟨s, by omega⟩).state
        (path ⟨s, by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s hs)) = true := by
  have hChoice :
      PathAssignmentChoiceTrue M x t path hPath
        (ntmChoiceVar M x t s
          (path ⟨s, by omega⟩).state
          (path ⟨s, by omega⟩).tape.head
          (choiceIdxOfStep M t path hPath s hs)) := by
    exact ⟨s, hs, hActive, rfl⟩
  simp [pathAssignment, hChoice]

theorem pathAssignment_choice_unselected
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hj : j < ntmBranchBound M + 1)
    (hneq :
      ¬ (NTMActive M (path ⟨s, by omega⟩) ∧
         q = (path ⟨s, by omega⟩).state ∧
         a = (path ⟨s, by omega⟩).tape.head ∧
         j = choiceIdxOfStep M t path hPath s hs)) :
    pathAssignment M x t path hPath (ntmChoiceVar M x t s q a j) = false := by
  have hnotState :
      ¬ PathAssignmentStateTrue M t path (ntmChoiceVar M x t s q a j) := by
    intro h
    rcases h with ⟨s', hs', heq⟩
    have hslt := ntmStateVar_lt_headBase M t s'
      (path ⟨s', by omega⟩).state hs'
    have hc := ntmChoiceVar_ge_choiceBase M x t s q a j
    have hb : ntmHeadBase M t <= ntmChoiceBase M x t := by
      simp [ntmChoiceBase, ntmRightBase, ntmLeftBase]
    omega
  have hnotHead :
      ¬ PathAssignmentHeadTrue M t path (ntmChoiceVar M x t s q a j) := by
    intro h
    rcases h with ⟨s', hs', heq⟩
    have hh := (ntmHeadVar_range M x t s'
      (path ⟨s', by omega⟩).tape.head hs').2
    have hc := ntmChoiceVar_ge_choiceBase M x t s q a j
    have hb : ntmLeftBase M x t <= ntmChoiceBase M x t := by
      simp [ntmChoiceBase, ntmRightBase]
    omega
  have hnotLeft :
      ¬ PathAssignmentLeftTrue M x t path (ntmChoiceVar M x t s q a j) := by
    intro h
    rcases h with ⟨s', hs', i', hi', heq⟩
    have hl := (ntmLeftVar_range M x t s' i'
      ((path ⟨s', by omega⟩).tape.left.getD i' M.machine.blank) hs' hi').2
    have hc := ntmChoiceVar_ge_choiceBase M x t s q a j
    have hb : ntmRightBase M x t <= ntmChoiceBase M x t := by
      simp [ntmChoiceBase]
    omega
  have hnotRight :
      ¬ PathAssignmentRightTrue M x t path (ntmChoiceVar M x t s q a j) := by
    intro h
    rcases h with ⟨s', hs', i', hi', heq⟩
    have hr := (ntmRightVar_range M x t s' i'
      ((path ⟨s', by omega⟩).tape.right.getD i' M.machine.blank) hs' hi').2
    have hc := ntmChoiceVar_ge_choiceBase M x t s q a j
    omega
  have hnotChoice :
      ¬ PathAssignmentChoiceTrue M x t path hPath (ntmChoiceVar M x t s q a j) := by
    intro h
    rcases h with ⟨s', hs', hactive', heq⟩
    have hj' := choiceIdxOfStep_lt_branchBound_succ M t path hPath s' hs' hactive'
    have hinj := ntmChoiceVar_injective M x t s s'
      q (path ⟨s', by omega⟩).state
      a (path ⟨s', by omega⟩).tape.head
      j (choiceIdxOfStep M t path hPath s' hs')
      hj hj' heq
    have hsEq := hinj.1
    subst s'
    apply hneq
    exact ⟨hactive', hinj.2.1, hinj.2.2.1, hinj.2.2.2⟩
  simp [pathAssignment, hnotState, hnotHead, hnotLeft, hnotRight, hnotChoice]


theorem pathAssignment_initial_state_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmSetStateClauses [] M t 0 M.machine.initial) = true := by
  rw [eval_ntmSetStateClauses_nil_iff]
  intro q
  rw [pathAssignment_state M x t path hPath 0 (by omega) q]
  have h0 := hPath.1
  change path 0 = initialNTMConfig M.machine x at h0
  have hstate : (path 0).state = M.machine.initial := by
    simpa [initialNTMConfig] using congrArg Configuration.state h0
  simpa [hstate, eq_comm]

theorem pathAssignment_initial_head_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head) = true := by
  rw [eval_ntmSetSymbolClauses_nil_iff]
  intro a
  rw [pathAssignment_head M x t path hPath 0 (by omega) a]
  have h0 := hPath.1
  change path 0 = initialNTMConfig M.machine x at h0
  have hhead : (path 0).tape.head = (inputTape x).head := by
    simpa [initialNTMConfig] using congrArg (fun c => c.tape.head) h0
  simpa [hhead, eq_comm]

theorem pathAssignment_initial_left_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank))) = true := by
  rw [evalNTMCNF_flatMap_range]
  intro i hi
  rw [eval_ntmSetLeftCell_nil_iff]
  intro b
  rw [pathAssignment_left M x t path hPath 0 (by omega) i hi b]
  have h0 := hPath.1
  change path 0 = initialNTMConfig M.machine x at h0
  have hleft :
      (path 0).tape.left.getD i M.machine.blank =
        (inputTape x).left.getD i M.machine.blank := by
    simpa [initialNTMConfig] using
      congrArg (fun c => c.tape.left.getD i M.machine.blank) h0
  rw [hleft]

theorem pathAssignment_initial_right_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank))) = true := by
  rw [evalNTMCNF_flatMap_range]
  intro i hi
  rw [eval_ntmSetRightCell_nil_iff]
  intro b
  rw [pathAssignment_right M x t path hPath 0 (by omega) i hi b]
  have h0 := hPath.1
  change path 0 = initialNTMConfig M.machine x at h0
  have hright :
      (path 0).tape.right.getD i M.machine.blank =
        (inputTape x).right.getD i M.machine.blank := by
    simpa [initialNTMConfig] using
      congrArg (fun c => c.tape.right.getD i M.machine.blank) h0
  rw [hright]

theorem pathAssignment_initial_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmInitialCNF M x t) = true := by
  let sigma := pathAssignment M x t path hPath
  let st := ntmSetStateClauses [] M t 0 M.machine.initial
  let hd := ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head
  let lf := (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetLeftCell [] M x t 0 i
      ((inputTape x).left.getD i M.machine.blank))
  let rt := (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetRightCell [] M x t 0 i
      ((inputTape x).right.getD i M.machine.blank))
  have hs : evalNTMCNF sigma st = true := by
    simpa [sigma, st] using pathAssignment_initial_state_sat M x t path hPath
  have hh : evalNTMCNF sigma hd = true := by
    simpa [sigma, hd] using pathAssignment_initial_head_sat M x t path hPath
  have hl : evalNTMCNF sigma lf = true := by
    simpa [sigma, lf] using pathAssignment_initial_left_sat M x t path hPath
  have hr : evalNTMCNF sigma rt = true := by
    simpa [sigma, rt] using pathAssignment_initial_right_sat M x t path hPath
  have hsh : evalNTMCNF sigma (st ++ hd) = true :=
    (evalNTMCNF_append sigma st hd).2 ⟨hs, hh⟩
  have hshl : evalNTMCNF sigma ((st ++ hd) ++ lf) = true :=
    (evalNTMCNF_append sigma (st ++ hd) lf).2 ⟨hsh, hl⟩
  have hall : evalNTMCNF sigma (((st ++ hd) ++ lf) ++ rt) = true :=
    (evalNTMCNF_append sigma ((st ++ hd) ++ lf) rt).2 ⟨hshl, hr⟩
  simpa [sigma, st, hd, lf, rt, ntmInitialCNF, List.append_assoc] using hall


theorem evalNTMClause_append_of_left_true
    (sigma : Assignment) (guard cl : NTMClause)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMClause sigma (guard ++ cl) = true := by
  induction guard with
  | nil =>
      simp [evalNTMClause] at hg
  | cons l ls ih =>
      simp [evalNTMClause] at hg ⊢
      rcases hg with hl | hls
      · exact Or.inl hl
      · exact Or.inr (ih hls)

theorem evalNTMCNF_of_all_mem_true
    (sigma : Assignment) (f : NTMCNF)
    (h : ∀ cl, cl ∈ f → evalNTMClause sigma cl = true) :
    evalNTMCNF sigma f = true := by
  induction f with
  | nil => rfl
  | cons cl rest ih =>
      rw [evalNTMCNF_cons_iff]
      exact ⟨h cl (by simp), ih (fun c hc => h c (by simp [hc]))⟩

theorem eval_setState_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmSetStateClauses guard M t s target) = true := by
  apply evalNTMCNF_of_all_mem_true
  intro cl hcl
  unfold ntmSetStateClauses at hcl
  rcases List.mem_ofFn.mp hcl with ⟨q, rfl⟩
  exact evalNTMClause_append_of_left_true sigma guard _ hg

theorem eval_setSymbol_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (varAt : Option Bool -> Nat) (target : Option Bool)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmSetSymbolClauses guard varAt target) = true := by
  apply evalNTMCNF_of_all_mem_true
  intro cl hcl
  unfold ntmSetSymbolClauses at hcl
  rcases List.mem_map.mp hcl with ⟨a, _, rfl⟩
  exact evalNTMClause_append_of_left_true sigma guard _ hg

theorem eval_copySymbol_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (oldVar newVar : Option Bool -> Nat)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmCopySymbolClauses guard oldVar newVar) = true := by
  apply evalNTMCNF_of_all_mem_true
  intro cl hcl
  unfold ntmCopySymbolClauses at hcl
  rcases List.mem_flatMap.mp hcl with ⟨a, _, hmem⟩
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact evalNTMClause_append_of_left_true sigma guard _ hg
  · exact evalNTMClause_append_of_left_true sigma guard _ hg

theorem pathAssignment_state_neg_of_ne
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (q : Fin (M.stateCount + 1))
    (hne : q ≠ (path ⟨s, by omega⟩).state) :
    evalNTMLiteral (pathAssignment M x t path hPath)
      (ntmNeg (ntmStateVar M t s q)) = true := by
  rw [show pathAssignment M x t path hPath (ntmStateVar M t s q) = false by
    rw [pathAssignment_state M x t path hPath s hs q]
    simp [hne]]
  simp [evalNTMLiteral, ntmNeg]

theorem pathAssignment_head_neg_of_ne
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (s : Nat) (hs : s <= t)
    (a : Option Bool)
    (hne : a ≠ (path ⟨s, by omega⟩).tape.head) :
    evalNTMLiteral (pathAssignment M x t path hPath)
      (ntmNeg (ntmHeadVar M t s a)) = true := by
  rw [show pathAssignment M x t path hPath (ntmHeadVar M t s a) = false by
    rw [pathAssignment_head M x t path hPath s hs a]
    simp [hne]]
  simp [evalNTMLiteral, ntmNeg]

theorem pathAssignment_case_guard_true_of_mismatch
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hmismatch :
      q ≠ (path ⟨s, by omega⟩).state ∨
      a ≠ (path ⟨s, by omega⟩).tape.head) :
    evalNTMClause (pathAssignment M x t path hPath)
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)] = true := by
  rcases hmismatch with hq | ha
  · simp [evalNTMClause,
      pathAssignment_state_neg_of_ne M x t path hPath s (by omega) q hq]
  · have hh := pathAssignment_head_neg_of_ne M x t path hPath s (by omega) a ha
    simp [evalNTMClause, hh]


theorem eval_copyLeftAll_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmCopyLeftAll guard M x t s) = true := by
  rw [show ntmCopyLeftAll guard M x t s =
      (List.range (ntmRadius x t)).flatMap (fun i =>
        ntmCopySymbolClauses guard
          (ntmLeftVar M x t s i)
          (ntmLeftVar M x t (s + 1) i)) by rfl]
  rw [evalNTMCNF_flatMap_range]
  intro i hi
  exact eval_copySymbol_guard_true sigma guard
    (ntmLeftVar M x t s i) (ntmLeftVar M x t (s + 1) i) hg

theorem eval_copyRightAll_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmCopyRightAll guard M x t s) = true := by
  rw [show ntmCopyRightAll guard M x t s =
      (List.range (ntmRadius x t)).flatMap (fun i =>
        ntmCopySymbolClauses guard
          (ntmRightVar M x t s i)
          (ntmRightVar M x t (s + 1) i)) by rfl]
  rw [evalNTMCNF_flatMap_range]
  intro i hi
  exact eval_copySymbol_guard_true sigma guard
    (ntmRightVar M x t s i) (ntmRightVar M x t (s + 1) i) hg

theorem eval_stayEffect_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmStayEffectCNF guard M x t s qNext write) = true := by
  let A := ntmSetStateClauses guard M t (s + 1) qNext
  let B := ntmSetSymbolClauses guard (ntmHeadVar M t (s + 1)) write
  let C := ntmCopyLeftAll guard M x t s
  let D := ntmCopyRightAll guard M x t s
  have hA : evalNTMCNF sigma A = true := by
    simpa [A] using eval_setState_guard_true sigma guard M t (s + 1) qNext hg
  have hB : evalNTMCNF sigma B = true := by
    simpa [B] using eval_setSymbol_guard_true sigma guard (ntmHeadVar M t (s + 1)) write hg
  have hC : evalNTMCNF sigma C = true := by
    simpa [C] using eval_copyLeftAll_guard_true sigma guard M x t s hg
  have hD : evalNTMCNF sigma D = true := by
    simpa [D] using eval_copyRightAll_guard_true sigma guard M x t s hg
  have hAB : evalNTMCNF sigma (A ++ B) = true :=
    (evalNTMCNF_append sigma A B).2 ⟨hA, hB⟩
  have hABC : evalNTMCNF sigma ((A ++ B) ++ C) = true :=
    (evalNTMCNF_append sigma (A ++ B) C).2 ⟨hAB, hC⟩
  have hABCD : evalNTMCNF sigma (((A ++ B) ++ C) ++ D) = true :=
    (evalNTMCNF_append sigma ((A ++ B) ++ C) D).2 ⟨hABC, hD⟩
  simpa [A, B, C, D, ntmStayEffectCNF, List.append_assoc] using hABCD

theorem eval_leftEffect_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmLeftEffectCNF guard M x t s qNext write) = true := by
  let A := ntmSetStateClauses guard M t (s + 1) qNext
  let B := ntmCopySymbolClauses guard
    (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1))
  let C := (List.range (ntmRadius x t - 1)).flatMap fun i =>
    ntmCopyLeftCell guard M x t s (i + 1) (s + 1) i
  let D := ntmSetLeftCell guard M x t (s + 1) (ntmRadius x t - 1) M.machine.blank
  let E := ntmSetRightCell guard M x t (s + 1) 0 write
  let F := (List.range (ntmRadius x t - 1)).flatMap fun i =>
    ntmCopyRightCell guard M x t s i (s + 1) (i + 1)
  have hA : evalNTMCNF sigma A = true := by
    simpa [A] using eval_setState_guard_true sigma guard M t (s + 1) qNext hg
  have hB : evalNTMCNF sigma B = true := by
    simpa [B] using eval_copySymbol_guard_true sigma guard
      (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)) hg
  have hC : evalNTMCNF sigma C = true := by
    rw [show C = (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyLeftCell guard M x t s (i + 1) (s + 1) i) by rfl]
    rw [evalNTMCNF_flatMap_range]
    intro i hi
    exact eval_copySymbol_guard_true sigma guard
      (ntmLeftVar M x t s (i + 1)) (ntmLeftVar M x t (s + 1) i) hg
  have hD : evalNTMCNF sigma D = true := by
    simpa [D] using eval_setSymbol_guard_true sigma guard
      (ntmLeftVar M x t (s + 1) (ntmRadius x t - 1)) M.machine.blank hg
  have hE : evalNTMCNF sigma E = true := by
    simpa [E] using eval_setSymbol_guard_true sigma guard
      (ntmRightVar M x t (s + 1) 0) write hg
  have hF : evalNTMCNF sigma F = true := by
    rw [show F = (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyRightCell guard M x t s i (s + 1) (i + 1)) by rfl]
    rw [evalNTMCNF_flatMap_range]
    intro i hi
    exact eval_copySymbol_guard_true sigma guard
      (ntmRightVar M x t s i) (ntmRightVar M x t (s + 1) (i + 1)) hg
  have hAB := (evalNTMCNF_append sigma A B).2 ⟨hA, hB⟩
  have hABC := (evalNTMCNF_append sigma (A ++ B) C).2 ⟨hAB, hC⟩
  have hABCD := (evalNTMCNF_append sigma ((A ++ B) ++ C) D).2 ⟨hABC, hD⟩
  have hABCDE := (evalNTMCNF_append sigma (((A ++ B) ++ C) ++ D) E).2 ⟨hABCD, hE⟩
  have hABCDEF := (evalNTMCNF_append sigma ((((A ++ B) ++ C) ++ D) ++ E) F).2 ⟨hABCDE, hF⟩
  simpa [A, B, C, D, E, F, ntmLeftEffectCNF, List.append_assoc] using hABCDEF

theorem eval_rightEffect_guard_true
    (sigma : Assignment) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool)
    (hg : evalNTMClause sigma guard = true) :
    evalNTMCNF sigma (ntmRightEffectCNF guard M x t s qNext write) = true := by
  let A := ntmSetStateClauses guard M t (s + 1) qNext
  let B := ntmCopySymbolClauses guard
    (ntmRightVar M x t s 0) (ntmHeadVar M t (s + 1))
  let C := ntmSetLeftCell guard M x t (s + 1) 0 write
  let D := (List.range (ntmRadius x t - 1)).flatMap fun i =>
    ntmCopyLeftCell guard M x t s i (s + 1) (i + 1)
  let E := (List.range (ntmRadius x t - 1)).flatMap fun i =>
    ntmCopyRightCell guard M x t s (i + 1) (s + 1) i
  let F := ntmSetRightCell guard M x t (s + 1) (ntmRadius x t - 1) M.machine.blank
  have hA : evalNTMCNF sigma A = true := by
    simpa [A] using eval_setState_guard_true sigma guard M t (s + 1) qNext hg
  have hB : evalNTMCNF sigma B = true := by
    simpa [B] using eval_copySymbol_guard_true sigma guard
      (ntmRightVar M x t s 0) (ntmHeadVar M t (s + 1)) hg
  have hC : evalNTMCNF sigma C = true := by
    simpa [C] using eval_setSymbol_guard_true sigma guard
      (ntmLeftVar M x t (s + 1) 0) write hg
  have hD : evalNTMCNF sigma D = true := by
    rw [show D = (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyLeftCell guard M x t s i (s + 1) (i + 1)) by rfl]
    rw [evalNTMCNF_flatMap_range]
    intro i hi
    exact eval_copySymbol_guard_true sigma guard
      (ntmLeftVar M x t s i) (ntmLeftVar M x t (s + 1) (i + 1)) hg
  have hE : evalNTMCNF sigma E = true := by
    rw [show E = (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyRightCell guard M x t s (i + 1) (s + 1) i) by rfl]
    rw [evalNTMCNF_flatMap_range]
    intro i hi
    exact eval_copySymbol_guard_true sigma guard
      (ntmRightVar M x t s (i + 1)) (ntmRightVar M x t (s + 1) i) hg
  have hF : evalNTMCNF sigma F = true := by
    simpa [F] using eval_setSymbol_guard_true sigma guard
      (ntmRightVar M x t (s + 1) (ntmRadius x t - 1)) M.machine.blank hg
  have hAB := (evalNTMCNF_append sigma A B).2 ⟨hA, hB⟩
  have hABC := (evalNTMCNF_append sigma (A ++ B) C).2 ⟨hAB, hC⟩
  have hABCD := (evalNTMCNF_append sigma ((A ++ B) ++ C) D).2 ⟨hABC, hD⟩
  have hABCDE := (evalNTMCNF_append sigma (((A ++ B) ++ C) ++ D) E).2 ⟨hABCD, hE⟩
  have hABCDEF := (evalNTMCNF_append sigma ((((A ++ B) ++ C) ++ D) ++ E) F).2 ⟨hABCDE, hF⟩
  simpa [A, B, C, D, E, F, ntmRightEffectCNF, List.append_assoc] using hABCDEF

theorem eval_choiceEffect_of_choice_false
    (sigma : Assignment)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (hfalse : sigma (ntmChoiceVar M x t s q a entry.1) = false) :
    evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true := by
  have hg :
      evalNTMClause sigma [ntmNeg (ntmChoiceVar M x t s q a entry.1)] = true := by
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, hfalse]
  rcases entry with ⟨j, qNext, write, d⟩
  cases d with
  | stay =>
      exact eval_stayEffect_guard_true sigma
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s qNext write hg
  | left =>
      exact eval_leftEffect_guard_true sigma
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s qNext write hg
  | right =>
      exact eval_rightEffect_guard_true sigma
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s qNext write hg

theorem pathAssignment_choice_false_of_mismatch
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hj : j < (M.machine.transition q a).length)
    (hmismatch :
      q ≠ (path ⟨s, by omega⟩).state ∨
      a ≠ (path ⟨s, by omega⟩).tape.head) :
    pathAssignment M x t path hPath (ntmChoiceVar M x t s q a j) = false := by
  apply pathAssignment_choice_unselected M x t path hPath s hs q a j
  · have hb := ntmBranchBound_ge_transition_length M q a
    omega
  · intro h
    rcases h with ⟨hactive, hq, ha, hjEq⟩
    rcases hmismatch with hqm | ham
    · exact hqm hq
    · exact ham ha


theorem pathAssignment_choiceGuard_sat_of_false
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hfalse : pathAssignment M x t path hPath
      (ntmChoiceVar M x t s q a j) = false) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmChoiceGuardCNF M x t s q a j) = true := by
  simp [ntmChoiceGuardCNF, evalNTMCNF, evalNTMClause,
    evalNTMLiteral, ntmNeg, hfalse]

theorem pathAssignment_guardChoiceClause_sat_of_mismatch
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hmismatch :
      q ≠ (path ⟨s, by omega⟩).state ∨
      a ≠ (path ⟨s, by omega⟩).tape.head) :
    evalNTMClause (pathAssignment M x t path hPath)
      (ntmGuardChoiceClause M x t s q a) = true := by
  have hg := pathAssignment_case_guard_true_of_mismatch
    M x t s path hPath hs q a hmismatch
  unfold ntmGuardChoiceClause
  exact evalNTMClause_append_of_left_true
    (pathAssignment M x t path hPath)
    [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
    ((ntmIndexedTransitions (M.machine.transition q a)).map
      (fun p => ntmPos (ntmChoiceVar M x t s q a p.1)))
    hg

theorem pathAssignment_atMostOne_sat_of_mismatch
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hmismatch :
      q ≠ (path ⟨s, by omega⟩).state ∨
      a ≠ (path ⟨s, by omega⟩).tape.head) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmAtMostOneChoiceCNF M x t s q a) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  let ids := entries.map Prod.fst
  unfold ntmAtMostOneChoiceCNF
  apply (evalNTMCNF_flatMap_list (pathAssignment M x t path hPath) ids
    (fun j => ids.flatMap fun k =>
      if j < k then
        [[ntmNeg (ntmChoiceVar M x t s q a j),
          ntmNeg (ntmChoiceVar M x t s q a k)]]
      else [])).2
  intro j hjmem
  apply (evalNTMCNF_flatMap_list (pathAssignment M x t path hPath) ids
    (fun k =>
      if j < k then
        [[ntmNeg (ntmChoiceVar M x t s q a j),
          ntmNeg (ntmChoiceVar M x t s q a k)]]
      else [])).2
  intro k hkmem
  by_cases hjk : j < k
  · have hjEntry : ∃ tr, (j, tr) ∈ entries := by
      simpa [ids] using hjmem
    rcases hjEntry with ⟨trj, hjEntry⟩
    have hkEntry : ∃ tr, (k, tr) ∈ entries := by
      simpa [ids] using hkmem
    rcases hkEntry with ⟨trk, hkEntry⟩
    have hjlt := indexedTransitions_index_lt
      (M.machine.transition q a) hjEntry
    have hklt := indexedTransitions_index_lt
      (M.machine.transition q a) hkEntry
    have hjfalse := pathAssignment_choice_false_of_mismatch
      M x t s path hPath hs q a j hjlt hmismatch
    have hkfalse := pathAssignment_choice_false_of_mismatch
      M x t s path hPath hs q a k hklt hmismatch
    simp [hjk, evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg,
      hjfalse, hkfalse]
  · simp [hjk, evalNTMCNF]

theorem pathAssignment_activeChoice_sat_of_mismatch
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hmismatch :
      q ≠ (path ⟨s, by omega⟩).state ∨
      a ≠ (path ⟨s, by omega⟩).tape.head) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmActiveChoiceCNF M x t s q a) = true := by
  let sigma := pathAssignment M x t path hPath
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have hfirst :
      evalNTMCNF sigma [ntmGuardChoiceClause M x t s q a] = true := by
    simp [evalNTMCNF,
      pathAssignment_guardChoiceClause_sat_of_mismatch
        M x t s path hPath hs q a hmismatch]
  have hguards :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true := by
    apply (evalNTMCNF_flatMap_list sigma entries
      (fun p => ntmChoiceGuardCNF M x t s q a p.1)).2
    intro p hp
    have hpLt := indexedTransitions_index_lt
      (M.machine.transition q a) hp
    have hpFalse := pathAssignment_choice_false_of_mismatch
      M x t s path hPath hs q a p.1 hpLt hmismatch
    exact pathAssignment_choiceGuard_sat_of_false
      M x t s path hPath q a p.1 hpFalse
  have hamo := pathAssignment_atMostOne_sat_of_mismatch
    M x t s path hPath hs q a hmismatch
  have heffects :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
    apply (evalNTMCNF_flatMap_list sigma entries
      (fun p => ntmChoiceEffectCNF M x t s q a p)).2
    intro p hp
    have hpLt := indexedTransitions_index_lt
      (M.machine.transition q a) hp
    have hpFalse := pathAssignment_choice_false_of_mismatch
      M x t s path hPath hs q a p.1 hpLt hmismatch
    exact eval_choiceEffect_of_choice_false sigma M x t s q a p hpFalse
  simp only [ntmActiveChoiceCNF, evalNTMCNF_append]
  exact ⟨⟨⟨hfirst, hguards⟩, hamo⟩, heffects⟩


theorem eval_haltedStutter_guard_true
    (sigma : Assignment)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hg :
      evalNTMClause sigma
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)] = true) :
    evalNTMCNF sigma (ntmHaltedStutterCNF M x t s q a) = true := by
  let guard := [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  let A := ntmSetStateClauses guard M t (s + 1) q
  let B := ntmCopyHeadCell guard M t s (s + 1)
  let C := ntmCopyLeftAll guard M x t s
  let D := ntmCopyRightAll guard M x t s
  have hA : evalNTMCNF sigma A = true := by
    simpa [A, guard] using eval_setState_guard_true sigma guard M t (s + 1) q hg
  have hB : evalNTMCNF sigma B = true := by
    simpa [B, guard, ntmCopyHeadCell] using eval_copySymbol_guard_true sigma guard
      (ntmHeadVar M t s) (ntmHeadVar M t (s + 1)) hg
  have hC : evalNTMCNF sigma C = true := by
    simpa [C, guard] using eval_copyLeftAll_guard_true sigma guard M x t s hg
  have hD : evalNTMCNF sigma D = true := by
    simpa [D, guard] using eval_copyRightAll_guard_true sigma guard M x t s hg
  have hAB := (evalNTMCNF_append sigma A B).2 ⟨hA, hB⟩
  have hABC := (evalNTMCNF_append sigma (A ++ B) C).2 ⟨hAB, hC⟩
  have hABCD := (evalNTMCNF_append sigma ((A ++ B) ++ C) D).2 ⟨hABC, hD⟩
  simpa [guard, A, B, C, D, ntmHaltedStutterCNF, List.append_assoc] using hABCD

theorem evalNTMClause_two_neg_prefix_of_tail_true
    (sigma : Assignment) (c1 c2 : Nat) (cl : NTMClause)
    (hc1 : sigma c1 = true) (hc2 : sigma c2 = true)
    (htail : evalNTMClause sigma cl = true) :
    evalNTMClause sigma (ntmNeg c1 :: ntmNeg c2 :: cl) = true := by
  simpa [evalNTMClause, evalNTMLiteral, ntmNeg, hc1, hc2] using htail

theorem eval_setState_two_neg_guard_of_exact
    (sigma : Assignment)
    (M : PolyNTMCandidate) (t s : Nat)
    (c1 c2 : Nat)
    (target : Fin (M.stateCount + 1))
    (hc1 : sigma c1 = true) (hc2 : sigma c2 = true)
    (hexact :
      forall r : Fin (M.stateCount + 1),
        sigma (ntmStateVar M t s r) = decide (r = target)) :
    evalNTMCNF sigma
      (ntmSetStateClauses [ntmNeg c1, ntmNeg c2] M t s target) = true := by
  unfold ntmSetStateClauses
  apply (evalNTMCNF_map_flatten_ofFn sigma
    (fun r : Fin (M.stateCount + 1) =>
      [[ntmNeg c1, ntmNeg c2] ++
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))])).2
  intro r
  have hunit :
      evalNTMClause sigma
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))] = true := by
    exact (evalNTMClause_singleton_litFor
      sigma (ntmStateVar M t s r) (decide (r = target))).2 (hexact r)
  simpa [evalNTMCNF] using
    evalNTMClause_two_neg_prefix_of_tail_true sigma c1 c2 _ hc1 hc2 hunit

theorem eval_copySymbol_two_neg_guard_of_eq
    (sigma : Assignment)
    (c1 c2 : Nat)
    (oldVar newVar : Option Bool -> Nat)
    (hc1 : sigma c1 = true) (hc2 : sigma c2 = true)
    (heq : forall b : Option Bool, sigma (newVar b) = sigma (oldVar b)) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses [ntmNeg c1, ntmNeg c2] oldVar newVar) = true := by
  apply (evalNTMCNF_flatMap_list sigma ntmAlphabet
    (fun b =>
      [[ntmNeg c1, ntmNeg c2] ++ [ntmNeg (oldVar b), ntmPos (newVar b)],
       [ntmNeg c1, ntmNeg c2] ++ [ntmPos (oldVar b), ntmNeg (newVar b)]])).2
  intro b hb
  cases hold : sigma (oldVar b) <;>
    have hn := heq b <;>
    rw [hold] at hn <;>
    simp [evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos,
      hc1, hc2, hold, hn]

theorem pathAssignment_haltedStutter_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hHalt : M.machine.accepting q = true ∨ M.machine.rejecting q = true) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmHaltedStutterCNF M x t s q a) = true := by
  by_cases hq : q = (path ⟨s, by omega⟩).state
  · by_cases ha : a = (path ⟨s, by omega⟩).tape.head
    · subst q
      subst a
      let c := path ⟨s, by omega⟩
      let c' := path ⟨s + 1, by omega⟩
      have hStep : NTMTableauStep M c c' := by
        simpa [c, c'] using hPath.2 ⟨s, hs⟩
      have hCHalt : NTMHalted M c := by
        simpa [NTMHalted, c] using hHalt
      have hEq : c' = c := by
        rcases hStep with hh | haStep
        · exact hh.2
        · exact False.elim (haStep.1 hCHalt)
      let sigma := pathAssignment M x t path hPath
      have hstate0 :
          sigma (ntmStateVar M t s c.state) = true := by
        simp [sigma, c, pathAssignment_state, hs]
      have hhead0 :
          sigma (ntmHeadVar M t s c.tape.head) = true := by
        simp [sigma, c, pathAssignment_head, hs]
      have hstateExact :
          forall r : Fin (M.stateCount + 1),
            sigma (ntmStateVar M t (s + 1) r) = decide (r = c.state) := by
        intro r
        rw [pathAssignment_state M x t path hPath (s + 1) (by omega) r]
        have hsEq : (path ⟨s + 1, by omega⟩).state = c.state := by
          simpa [c, c'] using congrArg Configuration.state hEq
        simpa [hsEq]
      have hheadEq :
          forall b : Option Bool,
            sigma (ntmHeadVar M t (s + 1) b) =
              sigma (ntmHeadVar M t s b) := by
        intro b
        rw [pathAssignment_head M x t path hPath (s + 1) (by omega) b]
        rw [pathAssignment_head M x t path hPath s (by omega) b]
        have hhEq :
            (path ⟨s + 1, by omega⟩).tape.head = c.tape.head := by
          simpa [c, c'] using congrArg (fun z => z.tape.head) hEq
        simpa [hhEq]
      have hleft :
          evalNTMCNF sigma
            (ntmCopyLeftAll
              [ntmNeg (ntmStateVar M t s c.state),
               ntmNeg (ntmHeadVar M t s c.tape.head)]
              M x t s) = true := by
        rw [show ntmCopyLeftAll
            [ntmNeg (ntmStateVar M t s c.state),
             ntmNeg (ntmHeadVar M t s c.tape.head)] M x t s =
          (List.range (ntmRadius x t)).flatMap (fun i =>
            ntmCopySymbolClauses
              [ntmNeg (ntmStateVar M t s c.state),
               ntmNeg (ntmHeadVar M t s c.tape.head)]
              (ntmLeftVar M x t s i)
              (ntmLeftVar M x t (s + 1) i)) by rfl]
        rw [evalNTMCNF_flatMap_range]
        intro i hi
        apply eval_copySymbol_two_neg_guard_of_eq sigma
          (ntmStateVar M t s c.state) (ntmHeadVar M t s c.tape.head)
          (ntmLeftVar M x t s i) (ntmLeftVar M x t (s + 1) i)
          hstate0 hhead0
        intro b
        rw [pathAssignment_left M x t path hPath (s + 1) (by omega) i hi b]
        rw [pathAssignment_left M x t path hPath s (by omega) i hi b]
        have hlEq :
            (path ⟨s + 1, by omega⟩).tape.left =
              c.tape.left := by
          simpa [c, c'] using congrArg (fun z => z.tape.left) hEq
        simpa [hlEq]
      have hright :
          evalNTMCNF sigma
            (ntmCopyRightAll
              [ntmNeg (ntmStateVar M t s c.state),
               ntmNeg (ntmHeadVar M t s c.tape.head)]
              M x t s) = true := by
        rw [show ntmCopyRightAll
            [ntmNeg (ntmStateVar M t s c.state),
             ntmNeg (ntmHeadVar M t s c.tape.head)] M x t s =
          (List.range (ntmRadius x t)).flatMap (fun i =>
            ntmCopySymbolClauses
              [ntmNeg (ntmStateVar M t s c.state),
               ntmNeg (ntmHeadVar M t s c.tape.head)]
              (ntmRightVar M x t s i)
              (ntmRightVar M x t (s + 1) i)) by rfl]
        rw [evalNTMCNF_flatMap_range]
        intro i hi
        apply eval_copySymbol_two_neg_guard_of_eq sigma
          (ntmStateVar M t s c.state) (ntmHeadVar M t s c.tape.head)
          (ntmRightVar M x t s i) (ntmRightVar M x t (s + 1) i)
          hstate0 hhead0
        intro b
        rw [pathAssignment_right M x t path hPath (s + 1) (by omega) i hi b]
        rw [pathAssignment_right M x t path hPath s (by omega) i hi b]
        have hrEq :
            (path ⟨s + 1, by omega⟩).tape.right =
              c.tape.right := by
          simpa [c, c'] using congrArg (fun z => z.tape.right) hEq
        simpa [hrEq]
      simp only [ntmHaltedStutterCNF, evalNTMCNF_append]
      refine ⟨eval_setState_two_neg_guard_of_exact sigma M t (s + 1)
          (ntmStateVar M t s c.state) (ntmHeadVar M t s c.tape.head)
          c.state hstate0 hhead0 hstateExact, ?_⟩
      refine ⟨eval_copySymbol_two_neg_guard_of_eq sigma
          (ntmStateVar M t s c.state) (ntmHeadVar M t s c.tape.head)
          (ntmHeadVar M t s) (ntmHeadVar M t (s + 1))
          hstate0 hhead0 hheadEq, ?_⟩
      exact ⟨hleft, hright⟩
    · have hg := pathAssignment_case_guard_true_of_mismatch
        M x t s path hPath hs q a (Or.inr ha)
      exact eval_haltedStutter_guard_true
        (pathAssignment M x t path hPath) M x t s q a hg
  · have hg := pathAssignment_case_guard_true_of_mismatch
      M x t s path hPath hs q a (Or.inl hq)
    exact eval_haltedStutter_guard_true
      (pathAssignment M x t path hPath) M x t s q a hg


structure PathTapeBoundAt
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (s : Nat) (hs : s <= t) : Prop where
  left_len : (path ⟨s, by omega⟩).tape.left.length <= x.length + s
  right_len : (path ⟨s, by omega⟩).tape.right.length <= x.length + s

theorem pathTapeBound_zero
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    PathTapeBoundAt M x t path 0 (by omega) := by
  have h0 := hPath.1
  change path 0 = initialNTMConfig M.machine x at h0
  refine { left_len := ?_, right_len := ?_ }
  · rw [h0]
    cases x <;> simp [initialNTMConfig, inputTape]
  · rw [h0]
    cases x <;> simp [initialNTMConfig, inputTape]

theorem pathTapeBound_step
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t)
    (hB : PathTapeBoundAt M x t path s (by omega)) :
    PathTapeBoundAt M x t path (s + 1) (by omega) := by
  let c := path ⟨s, by omega⟩
  let c' := path ⟨s + 1, by omega⟩
  have hStep : NTMTableauStep M c c' := by
    simpa [c, c'] using hPath.2 ⟨s, hs⟩
  rcases hStep with hhalt | hactive
  · have heq := hhalt.2
    refine { left_len := ?_, right_len := ?_ }
    · have hlen : c'.tape.left.length = c.tape.left.length := by
        simpa using congrArg (fun z => z.tape.left.length) heq
      rw [hlen]
      exact Nat.le_trans hB.left_len (by omega)
    · have hlen : c'.tape.right.length = c.tape.right.length := by
        simpa using congrArg (fun z => z.tape.right.length) heq
      rw [hlen]
      exact Nat.le_trans hB.right_len (by omega)
  · rcases active_step_transition_witness M c c' (Or.inr hactive)
      hactive.1 with ⟨tr, hmem, heq⟩
    rcases tr with ⟨qNext, write, d⟩
    cases d with
    | stay =>
        have heq' :
            c' = M.machine.stepBranch c (qNext, write, Direction.stay) := heq
        refine { left_len := ?_, right_len := ?_ }
        · have hl := congrArg (fun z => z.tape.left.length) heq'
          simp [NTM.stepBranch, Tape.write, Tape.move] at hl
          rw [hl]
          exact Nat.le_trans hB.left_len (by omega)
        · have hr := congrArg (fun z => z.tape.right.length) heq'
          simp [NTM.stepBranch, Tape.write, Tape.move] at hr
          rw [hr]
          exact Nat.le_trans hB.right_len (by omega)
    | left =>
        have heq' :
            c' = M.machine.stepBranch c (qNext, write, Direction.left) := heq
        have hlen := tapeMove_left_lengths M.machine.blank write c.tape
        refine { left_len := ?_, right_len := ?_ }
        · have hlEq := congrArg (fun z => z.tape.left.length) heq'
          simp [NTM.stepBranch] at hlEq
          rw [hlEq]
          exact Nat.le_trans hlen.1 (Nat.le_trans hB.left_len (by omega))
        · have hrEq := congrArg (fun z => z.tape.right.length) heq'
          simp [NTM.stepBranch] at hrEq
          rw [hrEq]
          exact Nat.le_trans hlen.2 (by omega)
    | right =>
        have heq' :
            c' = M.machine.stepBranch c (qNext, write, Direction.right) := heq
        have hlen := tapeMove_right_lengths M.machine.blank write c.tape
        refine { left_len := ?_, right_len := ?_ }
        · have hlEq := congrArg (fun z => z.tape.left.length) heq'
          simp [NTM.stepBranch] at hlEq
          rw [hlEq]
          exact Nat.le_trans hlen.1 (by omega)
        · have hrEq := congrArg (fun z => z.tape.right.length) heq'
          simp [NTM.stepBranch] at hrEq
          rw [hrEq]
          exact Nat.le_trans hlen.2 (Nat.le_trans hB.right_len (by omega))

theorem pathTapeBound_all
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    ∀ (s : Nat) (hs : s <= t), PathTapeBoundAt M x t path s hs := by
  intro s hs
  induction s with
  | zero =>
      simpa using pathTapeBound_zero M x t path hPath
  | succ s ih =>
      exact pathTapeBound_step M x t s path hPath (by omega) (ih (by omega))

theorem path_left_getD_outside
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s <= t) (hi : x.length + s <= i) :
    (path ⟨s, by omega⟩).tape.left.getD i M.machine.blank = M.machine.blank := by
  apply list_getD_eq_default_of_length_le
  exact Nat.le_trans (pathTapeBound_all M x t path hPath s hs).left_len hi

theorem path_right_getD_outside
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s <= t) (hi : x.length + s <= i) :
    (path ⟨s, by omega⟩).tape.right.getD i M.machine.blank = M.machine.blank := by
  apply list_getD_eq_default_of_length_le
  exact Nat.le_trans (pathTapeBound_all M x t path hPath s hs).right_len hi


theorem indexedTransitionsAux_get_mem
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (start j : Nat) (hj : j < ts.length) :
    (start + j, ts.get ⟨j, hj⟩) ∈ ntmIndexedTransitionsAux start ts := by
  induction ts generalizing start j with
  | nil =>
      simp at hj
  | cons tr rest ih =>
      cases j with
      | zero =>
          simp [ntmIndexedTransitionsAux]
      | succ j =>
          have hj' : j < rest.length := by
            simpa using hj
          have hmem := ih (start + 1) j hj'
          simpa [ntmIndexedTransitionsAux, Nat.add_assoc] using hmem

theorem indexedTransitions_get_mem
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat) (hj : j < ts.length) :
    (j, ts.get ⟨j, hj⟩) ∈ ntmIndexedTransitions ts := by
  unfold ntmIndexedTransitions
  simpa using indexedTransitionsAux_get_mem ts 0 j hj

theorem eval_setState_neg_guard_of_exact
    (sigma : Assignment)
    (M : PolyNTMCandidate) (t s : Nat)
    (cvar : Nat)
    (target : Fin (M.stateCount + 1))
    (hc : sigma cvar = true)
    (hexact :
      forall r : Fin (M.stateCount + 1),
        sigma (ntmStateVar M t s r) = decide (r = target)) :
    evalNTMCNF sigma
      (ntmSetStateClauses [ntmNeg cvar] M t s target) = true := by
  unfold ntmSetStateClauses
  apply (evalNTMCNF_map_flatten_ofFn sigma
    (fun r : Fin (M.stateCount + 1) =>
      [([ntmNeg cvar] ++
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))])])).2
  intro r
  have hunit :
      evalNTMClause sigma
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))] = true := by
    exact (evalNTMClause_singleton_litFor
      sigma (ntmStateVar M t s r) (decide (r = target))).2 (hexact r)
  simpa [evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, hc] using hunit

theorem eval_setSymbol_neg_guard_of_exact
    (sigma : Assignment)
    (cvar : Nat)
    (varAt : Option Bool -> Nat)
    (target : Option Bool)
    (hc : sigma cvar = true)
    (hexact : forall b : Option Bool, sigma (varAt b) = decide (b = target)) :
    evalNTMCNF sigma
      (ntmSetSymbolClauses [ntmNeg cvar] varAt target) = true := by
  unfold ntmSetSymbolClauses
  apply (evalNTMCNF_flatMap_list sigma ntmAlphabet
    (fun b => [([ntmNeg cvar] ++
      [ntmLitFor (varAt b) (decide (b = target))])])).2
  intro b hb
  have hunit :
      evalNTMClause sigma [ntmLitFor (varAt b) (decide (b = target))] = true := by
    exact (evalNTMClause_singleton_litFor sigma (varAt b)
      (decide (b = target))).2 (hexact b)
  simpa [evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, hc] using hunit

theorem eval_copySymbol_neg_guard_of_eq
    (sigma : Assignment)
    (cvar : Nat)
    (oldVar newVar : Option Bool -> Nat)
    (hc : sigma cvar = true)
    (heq : forall b : Option Bool, sigma (newVar b) = sigma (oldVar b)) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) = true := by
  apply (evalNTMCNF_flatMap_list sigma ntmAlphabet
    (fun b =>
      [[ntmNeg cvar] ++ [ntmNeg (oldVar b), ntmPos (newVar b)],
       [ntmNeg cvar] ++ [ntmPos (oldVar b), ntmNeg (newVar b)]])).2
  intro b hb
  cases hold : sigma (oldVar b) <;>
    have hn := heq b <;>
    rw [hold] at hn <;>
    simp [evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos,
      hc, hold, hn]

theorem pathAssignment_selected_effect_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t)
    (hActive : NTMActive M (path ⟨s, by omega⟩))
    (hj :
      choiceIdxOfStep M t path hPath s hs <
        (M.machine.transition
          (path ⟨s, by omega⟩).state
          (path ⟨s, by omega⟩).tape.head).length) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmChoiceEffectCNF M x t s
        (path ⟨s, by omega⟩).state
        (path ⟨s, by omega⟩).tape.head
        (choiceIdxOfStep M t path hPath s hs,
          (M.machine.transition
            (path ⟨s, by omega⟩).state
            (path ⟨s, by omega⟩).tape.head).get
              ⟨choiceIdxOfStep M t path hPath s hs, hj⟩)) = true := by
  let c := path ⟨s, by omega⟩
  let c' := path ⟨s + 1, by omega⟩
  let j := choiceIdxOfStep M t path hPath s hs
  let tr := (M.machine.transition c.state c.tape.head).get ⟨j, by simpa [c, j] using hj⟩
  have hStep : NTMTableauStep M c c' := by
    simpa [c, c'] using hPath.2 ⟨s, hs⟩
  have hW := active_step_transition_witness M c c' hStep hActive
  have hSpec := choiceIdxOfStep_active_spec M t path
    (by simpa using hPath) s hs hActive
  have htrEq : tr = hW.choose := by
    simpa [c, j, tr] using hSpec.choose_spec
  have hnext : c' = M.machine.stepBranch c tr := by
    rw [htrEq]
    exact hW.choose_spec.2.2
  have hchoice :
      pathAssignment M x t path hPath
        (ntmChoiceVar M x t s c.state c.tape.head j) = true := by
    simpa [c, j] using
      pathAssignment_choice_selected M x t path hPath s hs hActive
  rcases htrDef : tr with ⟨qNext, write, d⟩
  change
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmChoiceEffectCNF M x t s c.state c.tape.head (j, tr)) = true
  have hstateExact :
      forall r : Fin (M.stateCount + 1),
        pathAssignment M x t path hPath (ntmStateVar M t (s + 1) r) =
          decide (r = qNext) := by
    intro r
    rw [pathAssignment_state M x t path hPath (s + 1) (by omega) r]
    have hsEq : c'.state = qNext := by
      rw [hnext]
      simp [NTM.stepBranch, htrDef]
    simpa [c', hsEq]
  cases d with
  | stay =>
      have hheadExact :
          forall b : Option Bool,
            pathAssignment M x t path hPath (ntmHeadVar M t (s + 1) b) =
              decide (b = write) := by
        intro b
        rw [pathAssignment_head M x t path hPath (s + 1) (by omega) b]
        have hh : c'.tape.head = write := by
          rw [hnext]
          simp [NTM.stepBranch, Tape.write, Tape.move, htrDef]
        simpa [c', hh]
      have hleftEq :
          forall i : Nat, i < ntmRadius x t ->
            evalNTMCNF (pathAssignment M x t path hPath)
              (ntmCopySymbolClauses
                [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
                (ntmLeftVar M x t s i)
                (ntmLeftVar M x t (s + 1) i)) = true := by
        intro i hi
        apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
        intro b
        rw [pathAssignment_left M x t path hPath (s + 1) (by omega) i hi b]
        rw [pathAssignment_left M x t path hPath s (by omega) i hi b]
        have heq :
            c'.tape.left.getD i M.machine.blank =
              c.tape.left.getD i M.machine.blank := by
          rw [hnext]
          simp [NTM.stepBranch, Tape.write, Tape.move, htrDef]
        simpa [c, c', heq]
      have hrightEq :
          forall i : Nat, i < ntmRadius x t ->
            evalNTMCNF (pathAssignment M x t path hPath)
              (ntmCopySymbolClauses
                [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
                (ntmRightVar M x t s i)
                (ntmRightVar M x t (s + 1) i)) = true := by
        intro i hi
        apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
        intro b
        rw [pathAssignment_right M x t path hPath (s + 1) (by omega) i hi b]
        rw [pathAssignment_right M x t path hPath s (by omega) i hi b]
        have heq :
            c'.tape.right.getD i M.machine.blank =
              c.tape.right.getD i M.machine.blank := by
          rw [hnext]
          simp [NTM.stepBranch, Tape.write, Tape.move, htrDef]
        simpa [c, c', heq]
      rw [show
        ntmChoiceEffectCNF M x t s c.state c.tape.head (j, tr) =
          ntmStayEffectCNF
            [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
            M x t s qNext write by
        simp [ntmChoiceEffectCNF, htrDef]]
      unfold ntmStayEffectCNF
      rw [evalNTMCNF_append]
      refine ⟨eval_setState_neg_guard_of_exact
          (pathAssignment M x t path hPath) M t (s + 1)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          qNext hchoice hstateExact, ?_⟩
      rw [evalNTMCNF_append]
      refine ⟨eval_setSymbol_neg_guard_of_exact
          (pathAssignment M x t path hPath)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          (ntmHeadVar M t (s + 1)) write hchoice hheadExact, ?_⟩
      rw [evalNTMCNF_append]
      constructor
      · rw [show ntmCopyLeftAll
          [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)] M x t s =
          (List.range (ntmRadius x t)).flatMap (fun i =>
            ntmCopySymbolClauses
              [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
              (ntmLeftVar M x t s i) (ntmLeftVar M x t (s + 1) i)) by rfl]
        exact (evalNTMCNF_flatMap_range _ _ _).2 hleftEq
      · rw [show ntmCopyRightAll
          [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)] M x t s =
          (List.range (ntmRadius x t)).flatMap (fun i =>
            ntmCopySymbolClauses
              [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
              (ntmRightVar M x t s i) (ntmRightVar M x t (s + 1) i)) by rfl]
        exact (evalNTMCNF_flatMap_range _ _ _).2 hrightEq
  | left =>
      have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
      have hheadEq :
          forall b : Option Bool,
            pathAssignment M x t path hPath (ntmHeadVar M t (s + 1) b) =
              pathAssignment M x t path hPath (ntmLeftVar M x t s 0 b) := by
        intro b
        rw [pathAssignment_head M x t path hPath (s + 1) (by omega) b]
        rw [pathAssignment_left M x t path hPath s (by omega) 0 hrpos b]
        have heq :
            c'.tape.head = c.tape.left.getD 0 M.machine.blank := by
          rw [hnext]
          simpa [NTM.stepBranch, htrDef] using
            tapeMove_left_head M.machine.blank write c.tape
        simpa [c, c', heq]
      rw [show
        ntmChoiceEffectCNF M x t s c.state c.tape.head (j, tr) =
          ntmLeftEffectCNF
            [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
            M x t s qNext write by
        simp [ntmChoiceEffectCNF, htrDef]]
      unfold ntmLeftEffectCNF
      rw [evalNTMCNF_append]
      refine ⟨eval_setState_neg_guard_of_exact
          (pathAssignment M x t path hPath) M t (s + 1)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          qNext hchoice hstateExact, ?_⟩
      rw [evalNTMCNF_append]
      refine ⟨eval_copySymbol_neg_guard_of_eq
          (pathAssignment M x t path hPath)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1))
          hchoice hheadEq, ?_⟩
      rw [evalNTMCNF_append]
      refine ⟨?_, ?_⟩
      · rw [evalNTMCNF_flatMap_range]
        intro i hi
        apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
        intro b
        rw [pathAssignment_left M x t path hPath (s + 1) (by omega) i (by omega) b]
        rw [pathAssignment_left M x t path hPath s (by omega) (i + 1) (by omega) b]
        have heq :
            c'.tape.left.getD i M.machine.blank =
              c.tape.left.getD (i + 1) M.machine.blank := by
          rw [hnext]
          simpa [NTM.stepBranch, htrDef] using
            tapeMove_left_left_getD M.machine.blank write c.tape i
        simpa [c, c', heq]
      · refine ⟨?_, ?_⟩
        · apply eval_setSymbol_neg_guard_of_exact _ _
            (ntmLeftVar M x t (s + 1) (ntmRadius x t - 1))
            M.machine.blank hchoice
          intro b
          rw [pathAssignment_left M x t path hPath (s + 1) (by omega)
            (ntmRadius x t - 1) (by omega) b]
          have hout := path_left_getD_outside M x t s (ntmRadius x t)
            path hPath (by omega) (by simp [ntmRadius]; omega)
          have hcell :
              c'.tape.left.getD (ntmRadius x t - 1) M.machine.blank =
                M.machine.blank := by
            rw [hnext]
            have hm := tapeMove_left_left_getD M.machine.blank write c.tape
              (ntmRadius x t - 1)
            rw [hm]
            simpa [c, Nat.sub_add_cancel (by simp [ntmRadius] : 1 <= ntmRadius x t)]
              using hout
          simpa [c', hcell]
        · refine ⟨?_, ?_⟩
          · apply eval_setSymbol_neg_guard_of_exact _ _
              (ntmRightVar M x t (s + 1) 0) write hchoice
            intro b
            rw [pathAssignment_right M x t path hPath (s + 1) (by omega) 0 hrpos b]
            have hcell : c'.tape.right.getD 0 M.machine.blank = write := by
              rw [hnext]
              simpa [NTM.stepBranch, htrDef] using
                tapeMove_left_right_zero M.machine.blank write c.tape
            simpa [c', hcell]
          · rw [evalNTMCNF_flatMap_range]
            intro i hi
            apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
            intro b
            rw [pathAssignment_right M x t path hPath (s + 1) (by omega) (i + 1) (by omega) b]
            rw [pathAssignment_right M x t path hPath s (by omega) i (by omega) b]
            have heq :
                c'.tape.right.getD (i + 1) M.machine.blank =
                  c.tape.right.getD i M.machine.blank := by
              rw [hnext]
              simpa [NTM.stepBranch, htrDef] using
                tapeMove_left_right_succ M.machine.blank write c.tape i
            simpa [c, c', heq]
  | right =>
      have hrpos : 0 < ntmRadius x t := by simp [ntmRadius]
      have hheadEq :
          forall b : Option Bool,
            pathAssignment M x t path hPath (ntmHeadVar M t (s + 1) b) =
              pathAssignment M x t path hPath (ntmRightVar M x t s 0 b) := by
        intro b
        rw [pathAssignment_head M x t path hPath (s + 1) (by omega) b]
        rw [pathAssignment_right M x t path hPath s (by omega) 0 hrpos b]
        have heq :
            c'.tape.head = c.tape.right.getD 0 M.machine.blank := by
          rw [hnext]
          simpa [NTM.stepBranch, htrDef] using
            tapeMove_right_head M.machine.blank write c.tape
        simpa [c, c', heq]
      rw [show
        ntmChoiceEffectCNF M x t s c.state c.tape.head (j, tr) =
          ntmRightEffectCNF
            [ntmNeg (ntmChoiceVar M x t s c.state c.tape.head j)]
            M x t s qNext write by
        simp [ntmChoiceEffectCNF, htrDef]]
      unfold ntmRightEffectCNF
      rw [evalNTMCNF_append]
      refine ⟨eval_setState_neg_guard_of_exact
          (pathAssignment M x t path hPath) M t (s + 1)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          qNext hchoice hstateExact, ?_⟩
      refine ⟨eval_copySymbol_neg_guard_of_eq
          (pathAssignment M x t path hPath)
          (ntmChoiceVar M x t s c.state c.tape.head j)
          (ntmRightVar M x t s 0) (ntmHeadVar M t (s + 1))
          hchoice hheadEq, ?_⟩
      refine ⟨?_, ?_⟩
      · apply eval_setSymbol_neg_guard_of_exact _ _
          (ntmLeftVar M x t (s + 1) 0) write hchoice
        intro b
        rw [pathAssignment_left M x t path hPath (s + 1) (by omega) 0 hrpos b]
        have hcell : c'.tape.left.getD 0 M.machine.blank = write := by
          rw [hnext]
          simpa [NTM.stepBranch, htrDef] using
            tapeMove_right_left_zero M.machine.blank write c.tape
        simpa [c', hcell]
      · refine ⟨?_, ?_⟩
        · rw [evalNTMCNF_flatMap_range]
          intro i hi
          apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
          intro b
          rw [pathAssignment_left M x t path hPath (s + 1) (by omega) (i + 1) (by omega) b]
          rw [pathAssignment_left M x t path hPath s (by omega) i (by omega) b]
          have heq :
              c'.tape.left.getD (i + 1) M.machine.blank =
                c.tape.left.getD i M.machine.blank := by
            rw [hnext]
            simpa [NTM.stepBranch, htrDef] using
              tapeMove_right_left_succ M.machine.blank write c.tape i
          simpa [c, c', heq]
        · refine ⟨?_, ?_⟩
          · rw [evalNTMCNF_flatMap_range]
            intro i hi
            apply eval_copySymbol_neg_guard_of_eq _ _ _ _ hchoice
            intro b
            rw [pathAssignment_right M x t path hPath (s + 1) (by omega) i (by omega) b]
            rw [pathAssignment_right M x t path hPath s (by omega) (i + 1) (by omega) b]
            have heq :
                c'.tape.right.getD i M.machine.blank =
                  c.tape.right.getD (i + 1) M.machine.blank := by
              rw [hnext]
              simpa [NTM.stepBranch, htrDef] using
                tapeMove_right_right_getD M.machine.blank write c.tape i
            simpa [c, c', heq]
          · apply eval_setSymbol_neg_guard_of_exact _ _
              (ntmRightVar M x t (s + 1) (ntmRadius x t - 1))
              M.machine.blank hchoice
            intro b
            rw [pathAssignment_right M x t path hPath (s + 1) (by omega)
              (ntmRadius x t - 1) (by omega) b]
            have hout := path_right_getD_outside M x t s (ntmRadius x t)
              path hPath (by omega) (by simp [ntmRadius]; omega)
            have hcell :
                c'.tape.right.getD (ntmRadius x t - 1) M.machine.blank =
                  M.machine.blank := by
              rw [hnext]
              have hm := tapeMove_right_right_getD M.machine.blank write c.tape
                (ntmRadius x t - 1)
              rw [hm]
              simpa [c, Nat.sub_add_cancel (by simp [ntmRadius] : 1 <= ntmRadius x t)]
                using hout
            simpa [c', hcell]


theorem pathAssignment_actual_state_true
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s <= t) :
    pathAssignment M x t path hPath
      (ntmStateVar M t s (path ⟨s, by omega⟩).state) = true := by
  simp [pathAssignment_state M x t path hPath s hs]

theorem pathAssignment_actual_head_true
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    {c0 : NTMConfig M}
    (hPath : NTMTableauPath M t c0 path)
    (hs : s <= t) :
    pathAssignment M x t path hPath
      (ntmHeadVar M t s (path ⟨s, by omega⟩).tape.head) = true := by
  simp [pathAssignment_head M x t path hPath s hs]

theorem pathAssignment_activeChoice_actual_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t)
    (hActive : NTMActive M (path ⟨s, by omega⟩)) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmActiveChoiceCNF M x t s
        (path ⟨s, by omega⟩).state
        (path ⟨s, by omega⟩).tape.head) = true := by
  let q := (path ⟨s, by omega⟩).state
  let a := (path ⟨s, by omega⟩).tape.head
  let sigma := pathAssignment M x t path hPath
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  let j := choiceIdxOfStep M t path hPath s hs
  rcases choiceIdxOfStep_active_spec M t path (by simpa using hPath) s hs hActive with
    ⟨hj, hget⟩
  have hjBranch : j < ntmBranchBound M + 1 := by
    simpa [q, a, j] using
      choiceIdxOfStep_lt_branchBound_succ M t path (by simpa using hPath) s hs hActive
  have hjSel :
      sigma (ntmChoiceVar M x t s q a j) = true := by
    simpa [sigma, q, a, j] using
      pathAssignment_choice_selected M x t path hPath s hs hActive
  have hqTrue :
      sigma (ntmStateVar M t s q) = true := by
    simpa [sigma, q] using
      pathAssignment_actual_state_true M x t s path hPath (by omega)
  have haTrue :
      sigma (ntmHeadVar M t s a) = true := by
    simpa [sigma, a] using
      pathAssignment_actual_head_true M x t s path hPath (by omega)
  have hfirst :
      evalNTMCNF sigma [ntmGuardChoiceClause M x t s q a] = true := by
    have hjmem :
        (j, (M.machine.transition q a).get ⟨j, by simpa [q, a, j] using hj⟩) ∈ entries := by
      simpa [entries] using indexedTransitions_get_mem
        (M.machine.transition q a) j (by simpa [q, a, j] using hj)
    have htail :
        evalNTMClause sigma
          (entries.map (fun p => ntmPos (ntmChoiceVar M x t s q a p.1))) = true := by
      exact (evalNTMClause_map_pos_exists sigma entries
        (fun p => ntmChoiceVar M x t s q a p.1)).2
          ⟨(j, (M.machine.transition q a).get ⟨j, by simpa [q, a, j] using hj⟩),
            hjmem, by simpa [j] using hjSel⟩
    have hcl :
        evalNTMClause sigma (ntmGuardChoiceClause M x t s q a) = true := by
      unfold ntmGuardChoiceClause
      have happ := (evalNTMClause_append sigma
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        (entries.map (fun p => ntmPos (ntmChoiceVar M x t s q a p.1)))).2
          (Or.inr htail)
      simpa [entries] using happ
    simpa [evalNTMCNF] using hcl
  have hguards :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true := by
    apply (evalNTMCNF_flatMap_list sigma entries
      (fun p => ntmChoiceGuardCNF M x t s q a p.1)).2
    intro p hp
    simp [ntmChoiceGuardCNF, evalNTMCNF, evalNTMClause,
      evalNTMLiteral, ntmPos, hqTrue, haTrue]
  have hamo :
      evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true := by
    let ids := entries.map Prod.fst
    unfold ntmAtMostOneChoiceCNF
    apply (evalNTMCNF_flatMap_list sigma ids
      (fun r => ids.flatMap fun k =>
        if r < k then
          [[ntmNeg (ntmChoiceVar M x t s q a r),
            ntmNeg (ntmChoiceVar M x t s q a k)]]
        else [])).2
    intro r hrmem
    apply (evalNTMCNF_flatMap_list sigma ids
      (fun k =>
        if r < k then
          [[ntmNeg (ntmChoiceVar M x t s q a r),
            ntmNeg (ntmChoiceVar M x t s q a k)]]
        else [])).2
    intro k hkmem
    by_cases hrk : r < k
    · have hrEntry : ∃ tr, (r, tr) ∈ entries := by
        simpa [ids] using hrmem
      rcases hrEntry with ⟨trr, hrEntry⟩
      have hkEntry : ∃ tr, (k, tr) ∈ entries := by
        simpa [ids] using hkmem
      rcases hkEntry with ⟨trk, hkEntry⟩
      have hrlt := indexedTransitions_index_lt (M.machine.transition q a)
        (by simpa [entries] using hrEntry)
      have hklt := indexedTransitions_index_lt (M.machine.transition q a)
        (by simpa [entries] using hkEntry)
      by_cases hrj : r = j
      · subst r
        have hkj : k ≠ j := by omega
        have hkfalse :
            sigma (ntmChoiceVar M x t s q a k) = false := by
          apply pathAssignment_choice_unselected M x t path hPath s hs q a k
          · have hb := ntmBranchBound_ge_transition_length M q a
            omega
          · intro hbad
            rcases hbad with ⟨_, hqeq, haeq, hkeq⟩
            exact hkj hkeq
        simp [hrk, evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, hkfalse]
      · have hrfalse :
            sigma (ntmChoiceVar M x t s q a r) = false := by
          apply pathAssignment_choice_unselected M x t path hPath s hs q a r
          · have hb := ntmBranchBound_ge_transition_length M q a
            omega
          · intro hbad
            rcases hbad with ⟨_, hqeq, haeq, hreq⟩
            exact hrj hreq
        simp [hrk, evalNTMCNF, evalNTMClause, evalNTMLiteral, ntmNeg, hrfalse]
    · simp [hrk, evalNTMCNF]
  have heffects :
      evalNTMCNF sigma
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
    apply (evalNTMCNF_flatMap_list sigma entries
      (fun p => ntmChoiceEffectCNF M x t s q a p)).2
    intro p hp
    have hpLt := indexedTransitions_index_lt (M.machine.transition q a)
      (by simpa [entries] using hp)
    by_cases hpj : p.1 = j
    · rcases p with ⟨idx, trp⟩
      dsimp at hpj hpLt hp ⊢
      subst idx
      have hpVal :
          trp = (M.machine.transition q a).get
            ⟨j, by simpa using hpLt⟩ := by
        apply indexedTransitions_index_value (M.machine.transition q a) j trp
        · simpa [entries] using hp
        · simpa using hpLt
      subst trp
      simpa [q, a, j] using
        pathAssignment_selected_effect_sat M x t s path hPath hs hActive
          (by simpa [q, a, j] using hj)
    · have hpFalse :
          sigma (ntmChoiceVar M x t s q a p.1) = false := by
        apply pathAssignment_choice_unselected M x t path hPath s hs q a p.1
        · have hb := ntmBranchBound_ge_transition_length M q a
          omega
        · intro hbad
          rcases hbad with ⟨_, hqeq, haeq, hpeq⟩
          exact hpj hpeq
      exact eval_choiceEffect_of_choice_false sigma M x t s q a p hpFalse
  simp only [ntmActiveChoiceCNF, evalNTMCNF_append]
  exact ⟨hfirst, hguards, hamo, heffects⟩


theorem pathAssignment_transitionCase_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmTransitionCaseCNF M x t s q a) = true := by
  by_cases hHalt :
      M.machine.accepting q = true ∨ M.machine.rejecting q = true
  · simpa [ntmTransitionCaseCNF, hHalt] using
      pathAssignment_haltedStutter_sat M x t s path hPath hs q a hHalt
  · by_cases hq : q = (path ⟨s, by omega⟩).state
    · by_cases ha : a = (path ⟨s, by omega⟩).tape.head
      · subst q
        subst a
        have hActive :
            NTMActive M (path ⟨s, by omega⟩) := by
          exact hHalt
        simpa [ntmTransitionCaseCNF, hHalt] using
          pathAssignment_activeChoice_actual_sat M x t s path hPath hs hActive
      · simpa [ntmTransitionCaseCNF, hHalt] using
          pathAssignment_activeChoice_sat_of_mismatch
            M x t s path hPath hs q a (Or.inr ha)
    · simpa [ntmTransitionCaseCNF, hHalt] using
        pathAssignment_activeChoice_sat_of_mismatch
          M x t s path hPath hs q a (Or.inl hq)

theorem pathAssignment_transitionStep_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hs : s < t) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmTransitionStepCNF M x t s) = true := by
  apply (evalNTMCNF_map_flatten_ofFn
    (pathAssignment M x t path hPath)
    (fun q : Fin (M.stateCount + 1) =>
      ntmAlphabet.flatMap fun a =>
        ntmTransitionCaseCNF M x t s q a)).2
  intro q
  apply (evalNTMCNF_flatMap_list
    (pathAssignment M x t path hPath) ntmAlphabet
    (fun a => ntmTransitionCaseCNF M x t s q a)).2
  intro a ha
  exact pathAssignment_transitionCase_sat M x t s path hPath hs q a

theorem pathAssignment_transitions_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmTransitionsCNF M x t) = true := by
  rw [show ntmTransitionsCNF M x t =
    (List.range t).flatMap (fun s => ntmTransitionStepCNF M x t s) by rfl]
  rw [evalNTMCNF_flatMap_range]
  intro s hs
  exact pathAssignment_transitionStep_sat M x t s path hPath hs


theorem evalNTMClause_true_of_mem
    (sigma : Assignment) (cl : NTMClause) (lit : NTMLiteral)
    (hmem : lit ∈ cl)
    (hlit : evalNTMLiteral sigma lit = true) :
    evalNTMClause sigma cl = true := by
  induction cl with
  | nil =>
      simp at hmem
  | cons l ls ih =>
      simp only [List.mem_cons] at hmem
      simp [evalNTMClause]
      rcases hmem with rfl | hmem
      · exact Or.inl hlit
      · exact Or.inr (ih hmem)

theorem pathAssignment_final_clause_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hAcc : M.machine.accepting (path (Fin.last t)).state = true) :
    evalNTMClause (pathAssignment M x t path hPath)
      (ntmAcceptingStateLits M t) = true := by
  let q : Fin (M.stateCount + 1) := (path (Fin.last t)).state
  have hqPath :
      q = (path ⟨t, by omega⟩).state := by
    rfl
  have hqAcc : M.machine.accepting q = true := by
    simpa [q] using hAcc
  have hmem :
      ntmPos (ntmStateVar M t t q) ∈ ntmAcceptingStateLits M t := by
    unfold ntmAcceptingStateLits
    simp [hqAcc]
  have hvar :
      pathAssignment M x t path hPath (ntmStateVar M t t q) = true := by
    rw [pathAssignment_state M x t path hPath t (by omega) q]
    simp [hqPath]
  apply evalNTMClause_true_of_mem
    (pathAssignment M x t path hPath)
    (ntmAcceptingStateLits M t)
    (ntmPos (ntmStateVar M t t q)) hmem
  simp [evalNTMLiteral, ntmPos, hvar]

theorem pathAssignment_final_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hAcc : M.machine.accepting (path (Fin.last t)).state = true) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (ntmFinalAcceptanceCNF M t) = true := by
  simpa [ntmFinalAcceptanceCNF, evalNTMCNF] using
    pathAssignment_final_clause_sat M x t path hPath hAcc

theorem pathAssignment_boundedExec_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (path : Fin (t + 1) -> NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path)
    (hAcc : M.machine.accepting (path (Fin.last t)).state = true) :
    evalNTMCNF (pathAssignment M x t path hPath)
      (boundedExecTableauCNF_NTM M x t) = true := by
  have hi := pathAssignment_initial_sat M x t path hPath
  have ht := pathAssignment_transitions_sat M x t path hPath
  have hf := pathAssignment_final_sat M x t path hPath hAcc
  rw [show boundedExecTableauCNF_NTM M x t =
      ntmInitialCNF M x t ++
      ntmTransitionsCNF M x t ++
      ntmFinalAcceptanceCNF M t by rfl]
  rw [evalNTMCNF_append]
  exact ⟨hi, (evalNTMCNF_append _ _ _).2 ⟨ht, hf⟩⟩

theorem tableau_completeness_assignment
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (hAcc : M.machine.AcceptsWithin t (initialNTMConfig M.machine x)) :
    ∃ sigma : Assignment,
      evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true := by
  rcases acceptsWithin_to_path M t (initialNTMConfig M.machine x) hAcc with
    ⟨path, hPath, hFinal⟩
  exact ⟨pathAssignment M x t path hPath,
    pathAssignment_boundedExec_sat M x t path hPath hFinal⟩

theorem tableau_completeness_to_satLanguage
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (hAcc : M.machine.AcceptsWithin t (initialNTMConfig M.machine x)) :
    SATLanguage (boundedExecCircuit_NTM M x t) := by
  rw [show boundedExecCircuit_NTM M x t =
    ntmCNFCircuit (boundedExecTableauCNF_NTM M x t) by rfl]
  exact (satLanguage_ntmCNFCircuit_iff
    (boundedExecTableauCNF_NTM M x t)).2
      (tableau_completeness_assignment M x t hAcc)

theorem tableau_soundness_from_satLanguage
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (hSat : SATLanguage (boundedExecCircuit_NTM M x t)) :
    M.machine.AcceptsWithin t (initialNTMConfig M.machine x) := by
  rw [show boundedExecCircuit_NTM M x t =
    ntmCNFCircuit (boundedExecTableauCNF_NTM M x t) by rfl] at hSat
  rcases (satLanguage_ntmCNFCircuit_iff
    (boundedExecTableauCNF_NTM M x t)).1 hSat with ⟨sigma, hsigma⟩
  exact tableau_soundness_from_assignment M x t sigma hsigma

theorem tableau_correctness_iff
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    SATLanguage (boundedExecCircuit_NTM M x t) <->
      M.machine.AcceptsWithin t (initialNTMConfig M.machine x) := by
  constructor
  · exact tableau_soundness_from_satLanguage M x t
  · exact tableau_completeness_to_satLanguage M x t


def ntmClauseWeight (cl : NTMClause) : Nat :=
  cl.length + 1

def ntmCNFWeight (f : NTMCNF) : Nat :=
  f.foldl (fun acc cl => acc + ntmClauseWeight cl) 0

def ntmClauseMaxVar (cl : NTMClause) : Nat :=
  cl.foldl (fun acc l => Nat.max acc l.var) 0

def ntmCNFMaxVar (f : NTMCNF) : Nat :=
  f.foldl (fun acc cl => Nat.max acc (ntmClauseMaxVar cl)) 0

theorem encodeNat_length_exact
    (n : Nat) :
    (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, ih, Nat.add_assoc]

theorem ntmLiteralCircuit_encoding_le
    (l : NTMLiteral) :
    (encodeCircuit (ntmLiteralCircuit l)).length <=
      7 * (l.var + 1) := by
  cases l with
  | mk v p =>
      cases p <;>
        simp [ntmLiteralCircuit, encodeCircuit, encodeNat_length_exact] <;>
        omega

theorem ntmClauseMaxVar_ge_of_mem
    (cl : NTMClause) (l : NTMLiteral)
    (hl : l ∈ cl) :
    l.var <= ntmClauseMaxVar cl := by
  unfold ntmClauseMaxVar
  apply foldl_max_ge_of_mem (cl.map NTMLiteral.var) l.var 0
  exact List.mem_map.mpr ⟨l, hl, rfl⟩

theorem ntmCNFMaxVar_ge_clause
    (f : NTMCNF) (cl : NTMClause)
    (hcl : cl ∈ f) :
    ntmClauseMaxVar cl <= ntmCNFMaxVar f := by
  unfold ntmCNFMaxVar
  apply foldl_max_ge_of_mem (f.map ntmClauseMaxVar) (ntmClauseMaxVar cl) 0
  exact List.mem_map.mpr ⟨cl, hcl, rfl⟩

theorem ntmClauseCircuit_encoding_le
    (cl : NTMClause) :
    (encodeCircuit (ntmClauseCircuit cl)).length <=
      10 * ntmClauseWeight cl * (ntmClauseMaxVar cl + 1) := by
  induction cl with
  | nil =>
      simp [ntmClauseCircuit, ntmClauseWeight, encodeCircuit]
  | cons l ls ih =>
      have hlmax : l.var <= ntmClauseMaxVar (l :: ls) := by
        unfold ntmClauseMaxVar
        simp only [List.foldl_cons]
        exact Nat.le_max_right _ _
      have htail :
          ntmClauseMaxVar ls <= ntmClauseMaxVar (l :: ls) := by
        unfold ntmClauseMaxVar
        simp only [List.foldl_cons]
        induction ls with
        | nil => simp
        | cons a as ihls =>
            simp only [List.foldl_cons]
            exact foldl_max_ge_acc (as.map NTMLiteral.var)
              (Nat.max (Nat.max 0 l.var) a.var)
      have hlit := ntmLiteralCircuit_encoding_le l
      simp [ntmClauseCircuit, encodeCircuit, ntmClauseWeight] at ih ⊢
      nlinarith

theorem ntmCNFCircuit_encoding_le
    (f : NTMCNF) :
    (encodeCircuit (ntmCNFCircuit f)).length <=
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1) + 3 := by
  induction f with
  | nil =>
      simp [ntmCNFCircuit, ntmCNFWeight, encodeCircuit]
  | cons cl fs ih =>
      have hclmax :
          ntmClauseMaxVar cl <= ntmCNFMaxVar (cl :: fs) := by
        apply ntmCNFMaxVar_ge_clause
        simp
      have htailmax :
          ntmCNFMaxVar fs <= ntmCNFMaxVar (cl :: fs) := by
        unfold ntmCNFMaxVar
        simp only [List.foldl_cons]
        induction fs with
        | nil => simp
        | cons a as as ihfs =>
            simp only [List.foldl_cons]
            exact foldl_max_ge_acc (as.map ntmClauseMaxVar)
              (Nat.max (Nat.max 0 (ntmClauseMaxVar cl)) (ntmClauseMaxVar a))
      have hcl := ntmClauseCircuit_encoding_le cl
      simp [ntmCNFCircuit, encodeCircuit, ntmCNFWeight, ntmClauseWeight] at ih ⊢
      nlinarith


def tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmChoiceBase M x t +
    ((((t * ntmStateCount M + M.stateCount) * 3 + 2) *
      (ntmBranchBound M + 1)) + ntmBranchBound M)

theorem ntmStateVar_lt_tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (hs : s <= t) :
    ntmStateVar M t s q < tableauVarCap M x t := by
  have h1 := ntmStateVar_lt_headBase M t s q hs
  have h2 : ntmHeadBase M t <= ntmChoiceBase M x t := by
    simp [ntmChoiceBase, ntmRightBase, ntmLeftBase]
  unfold tableauVarCap
  omega

theorem ntmHeadVar_lt_tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (a : Option Bool) (hs : s <= t) :
    ntmHeadVar M t s a < tableauVarCap M x t := by
  have h1 := (ntmHeadVar_range M x t s a hs).2
  have h2 : ntmLeftBase M x t <= ntmChoiceBase M x t := by
    simp [ntmChoiceBase, ntmRightBase]
  unfold tableauVarCap
  omega

theorem ntmLeftVar_lt_tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) (hs : s <= t) (hi : i < ntmRadius x t) :
    ntmLeftVar M x t s i a < tableauVarCap M x t := by
  have h1 := (ntmLeftVar_range M x t s i a hs hi).2
  have h2 : ntmRightBase M x t <= ntmChoiceBase M x t := by
    simp [ntmChoiceBase]
  unfold tableauVarCap
  omega

theorem ntmRightVar_lt_tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) (hs : s <= t) (hi : i < ntmRadius x t) :
    ntmRightVar M x t s i a < tableauVarCap M x t := by
  have h1 := (ntmRightVar_range M x t s i a hs hi).2
  unfold tableauVarCap
  omega

theorem ntmChoiceVar_le_tableauVarCap
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) (j : Nat)
    (hs : s <= t)
    (hj : j <= ntmBranchBound M) :
    ntmChoiceVar M x t s q a j <= tableauVarCap M x t := by
  have hq : q.val <= M.stateCount := by
    omega
  have ha : ntmSymbolCode a <= 2 := by
    have := ntmSymbolCode_lt_three a
    omega
  simp [ntmChoiceVar, tableauVarCap, ntmStateCount]
  nlinarith

def ClauseVarsLe (cap : Nat) (cl : NTMClause) : Prop :=
  forall l, l ∈ cl -> l.var <= cap

def CNFVarsLe (cap : Nat) (f : NTMCNF) : Prop :=
  forall cl, cl ∈ f -> ClauseVarsLe cap cl

theorem ClauseVarsLe_append
    {cap : Nat} {a b : NTMClause}
    (ha : ClauseVarsLe cap a)
    (hb : ClauseVarsLe cap b) :
    ClauseVarsLe cap (a ++ b) := by
  intro l hl
  rw [List.mem_append] at hl
  rcases hl with hl | hl
  · exact ha l hl
  · exact hb l hl

theorem CNFVarsLe_append
    {cap : Nat} {a b : NTMCNF}
    (ha : CNFVarsLe cap a)
    (hb : CNFVarsLe cap b) :
    CNFVarsLe cap (a ++ b) := by
  intro cl hcl
  rw [List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact ha cl hcl
  · exact hb cl hcl

theorem ntmClauseMaxVar_le_of_varsLe
    (cap : Nat) (cl : NTMClause)
    (h : ClauseVarsLe cap cl) :
    ntmClauseMaxVar cl <= cap := by
  unfold ntmClauseMaxVar
  apply foldl_max_le_of_all_le (cl.map NTMLiteral.var) 0 cap (by omega)
  intro v hv
  rw [List.mem_map] at hv
  rcases hv with ⟨l, hl, rfl⟩
  exact h l hl

theorem ntmCNFMaxVar_le_of_varsLe
    (cap : Nat) (f : NTMCNF)
    (h : CNFVarsLe cap f) :
    ntmCNFMaxVar f <= cap := by
  unfold ntmCNFMaxVar
  apply foldl_max_le_of_all_le (f.map ntmClauseMaxVar) 0 cap (by omega)
  intro v hv
  rw [List.mem_map] at hv
  rcases hv with ⟨cl, hcl, rfl⟩
  exact ntmClauseMaxVar_le_of_varsLe cap cl (h cl hcl)

theorem literalVar_le_cap_state
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (hs : s <= t) :
    (ntmPos (ntmStateVar M t s q)).var <= tableauVarCap M x t := by
  simp [ntmPos]
  exact Nat.le_of_lt (ntmStateVar_lt_tableauVarCap M x t s q hs)

theorem literalVar_le_cap_head
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (a : Option Bool) (hs : s <= t) :
    (ntmPos (ntmHeadVar M t s a)).var <= tableauVarCap M x t := by
  simp [ntmPos]
  exact Nat.le_of_lt (ntmHeadVar_lt_tableauVarCap M x t s a hs)


theorem ntmClauseWeight_append
    (a b : NTMClause) :
    ntmClauseWeight (a ++ b) =
      ntmClauseWeight a + b.length := by
  simp [ntmClauseWeight]

theorem ntmCNFWeight_append
    (a b : NTMCNF) :
    ntmCNFWeight (a ++ b) = ntmCNFWeight a + ntmCNFWeight b := by
  unfold ntmCNFWeight
  induction a with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.cons_append]
      simpa [Nat.add_assoc] using ih

theorem ntmCNFWeight_flatMap_range_le
    (n K : Nat) (f : Nat -> NTMCNF)
    (h : forall i < n, ntmCNFWeight (f i) <= K) :
    ntmCNFWeight ((List.range n).flatMap f) <= n * K := by
  induction n with
  | zero => simp [ntmCNFWeight]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ntmCNFWeight_append]
      have hprev := ih (fun i hi => h i (by omega))
      have hlast := h n (by omega)
      nlinarith

theorem ntmCNFWeight_flatMap_list_le
    {α : Type}
    (xs : List α) (K : Nat) (f : α -> NTMCNF)
    (h : forall a, a ∈ xs -> ntmCNFWeight (f a) <= K) :
    ntmCNFWeight (xs.flatMap f) <= xs.length * K := by
  induction xs with
  | nil => simp [ntmCNFWeight]
  | cons a as ih =>
      rw [List.flatMap_cons, ntmCNFWeight_append]
      have ha := h a (by simp)
      have ht := ih (fun z hz => h z (by simp [hz]))
      simp at *
      nlinarith

theorem ntmSetState_weight
    (guard : NTMClause)
    (M : PolyNTMCandidate) (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    ntmCNFWeight (ntmSetStateClauses guard M t s target) =
      ntmStateCount M * (guard.length + 2) := by
  unfold ntmSetStateClauses ntmCNFWeight ntmClauseWeight ntmStateCount
  simp

theorem ntmSetSymbol_weight
    (guard : NTMClause)
    (varAt : Option Bool -> Nat) (target : Option Bool) :
    ntmCNFWeight (ntmSetSymbolClauses guard varAt target) =
      3 * (guard.length + 2) := by
  cases target <;>
    simp [ntmSetSymbolClauses, ntmAlphabet, ntmCNFWeight, ntmClauseWeight]

theorem ntmCopySymbol_weight
    (guard : NTMClause)
    (oldVar newVar : Option Bool -> Nat) :
    ntmCNFWeight (ntmCopySymbolClauses guard oldVar newVar) =
      6 * (guard.length + 3) := by
  simp [ntmCopySymbolClauses, ntmAlphabet, ntmCNFWeight, ntmClauseWeight]
  ring

theorem ntmCopyLeftAll_weight
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) :
    ntmCNFWeight (ntmCopyLeftAll guard M x t s) =
      ntmRadius x t * (6 * (guard.length + 3)) := by
  unfold ntmCopyLeftAll
  have hconst :
      forall i < ntmRadius x t,
        ntmCNFWeight
          (ntmCopySymbolClauses guard
            (ntmLeftVar M x t s i)
            (ntmLeftVar M x t (s + 1) i)) =
          6 * (guard.length + 3) := by
    intro i hi
    exact ntmCopySymbol_weight guard _ _
  induction ntmRadius x t with
  | zero => simp [ntmCNFWeight]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ntmCNFWeight_append]
      simp only [List.flatMap_singleton]
      rw [ntmCopySymbol_weight]
      have := ih
      nlinarith

theorem ntmCopyRightAll_weight
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) :
    ntmCNFWeight (ntmCopyRightAll guard M x t s) =
      ntmRadius x t * (6 * (guard.length + 3)) := by
  unfold ntmCopyRightAll
  induction ntmRadius x t with
  | zero => simp [ntmCNFWeight]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ntmCNFWeight_append]
      simp only [List.flatMap_singleton]
      rw [ntmCopySymbol_weight]
      nlinarith

theorem ntmInitial_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmCNFWeight (ntmInitialCNF M x t) <=
      2 * ntmStateCount M + 6 + 12 * ntmRadius x t := by
  unfold ntmInitialCNF
  rw [ntmCNFWeight_append, ntmCNFWeight_append, ntmCNFWeight_append]
  rw [ntmSetState_weight, ntmSetSymbol_weight]
  have hl := ntmCNFWeight_flatMap_range_le
    (ntmRadius x t) 6
    (fun i => ntmSetLeftCell [] M x t 0 i
      ((inputTape x).left.getD i M.machine.blank))
    (by
      intro i hi
      simpa [ntmSetLeftCell] using
        ntmSetSymbol_weight ([] : NTMClause)
          (ntmLeftVar M x t 0 i)
          ((inputTape x).left.getD i M.machine.blank))
  have hr := ntmCNFWeight_flatMap_range_le
    (ntmRadius x t) 6
    (fun i => ntmSetRightCell [] M x t 0 i
      ((inputTape x).right.getD i M.machine.blank))
    (by
      intro i hi
      simpa [ntmSetRightCell] using
        ntmSetSymbol_weight ([] : NTMClause)
          (ntmRightVar M x t 0 i)
          ((inputTape x).right.getD i M.machine.blank))
  nlinarith

theorem ntmHaltedStutter_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    ntmCNFWeight (ntmHaltedStutterCNF M x t s q a) <=
      4 * ntmStateCount M + 30 + 60 * ntmRadius x t := by
  let guard : NTMClause :=
    [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  simp only [ntmHaltedStutterCNF, ntmCNFWeight_append]
  rw [ntmSetState_weight, ntmCopySymbol_weight,
      ntmCopyLeftAll_weight, ntmCopyRightAll_weight]
  simp [guard]
  ring_nf
  omega

def ntmEffectWeightCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  3 * ntmStateCount M + 50 + 48 * ntmRadius x t

theorem ntmChoiceEffect_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction)) :
    ntmCNFWeight (ntmChoiceEffectCNF M x t s q a entry) <=
      ntmEffectWeightCap M x t := by
  rcases entry with ⟨j, qNext, write, d⟩
  cases d with
  | stay =>
      simp [ntmChoiceEffectCNF, ntmStayEffectCNF,
        ntmEffectWeightCap, ntmCNFWeight_append,
        ntmSetState_weight, ntmSetSymbol_weight,
        ntmCopyLeftAll_weight, ntmCopyRightAll_weight]
      nlinarith
  | left =>
      unfold ntmChoiceEffectCNF ntmLeftEffectCNF ntmEffectWeightCap
      simp only [ntmCNFWeight_append]
      rw [ntmSetState_weight, ntmCopySymbol_weight]
      have hsl := ntmCNFWeight_flatMap_range_le
        (ntmRadius x t - 1) 24
        (fun i => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
          M x t s (i + 1) (s + 1) i)
        (by
          intro i hi
          simpa [ntmCopyLeftCell] using
            ntmCopySymbol_weight
              [ntmNeg (ntmChoiceVar M x t s q a j)]
              (ntmLeftVar M x t s (i+1))
              (ntmLeftVar M x t (s+1) i))
      have hsr := ntmCNFWeight_flatMap_range_le
        (ntmRadius x t - 1) 24
        (fun i => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
          M x t s i (s + 1) (i + 1))
        (by
          intro i hi
          simpa [ntmCopyRightCell] using
            ntmCopySymbol_weight
              [ntmNeg (ntmChoiceVar M x t s q a j)]
              (ntmRightVar M x t s i)
              (ntmRightVar M x t (s+1) (i+1)))
      rw [show ntmCNFWeight
          (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
            M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = 9 by
        simpa [ntmSetLeftCell] using
          ntmSetSymbol_weight [ntmNeg (ntmChoiceVar M x t s q a j)]
            (ntmLeftVar M x t (s+1) (ntmRadius x t - 1)) M.machine.blank]
      rw [show ntmCNFWeight
          (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
            M x t (s + 1) 0 write) = 9 by
        simpa [ntmSetRightCell] using
          ntmSetSymbol_weight [ntmNeg (ntmChoiceVar M x t s q a j)]
            (ntmRightVar M x t (s+1) 0) write]
      nlinarith
  | right =>
      unfold ntmChoiceEffectCNF ntmRightEffectCNF ntmEffectWeightCap
      simp only [ntmCNFWeight_append]
      rw [ntmSetState_weight, ntmCopySymbol_weight]
      have hsl := ntmCNFWeight_flatMap_range_le
        (ntmRadius x t - 1) 24
        (fun i => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
          M x t s i (s + 1) (i + 1))
        (by
          intro i hi
          simpa [ntmCopyLeftCell] using
            ntmCopySymbol_weight
              [ntmNeg (ntmChoiceVar M x t s q a j)]
              (ntmLeftVar M x t s i)
              (ntmLeftVar M x t (s+1) (i+1)))
      have hsr := ntmCNFWeight_flatMap_range_le
        (ntmRadius x t - 1) 24
        (fun i => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
          M x t s (i + 1) (s + 1) i)
        (by
          intro i hi
          simpa [ntmCopyRightCell] using
            ntmCopySymbol_weight
              [ntmNeg (ntmChoiceVar M x t s q a j)]
              (ntmRightVar M x t s (i+1))
              (ntmRightVar M x t (s+1) i))
      rw [show ntmCNFWeight
          (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
            M x t (s + 1) 0 write) = 9 by
        simpa [ntmSetLeftCell] using
          ntmSetSymbol_weight [ntmNeg (ntmChoiceVar M x t s q a j)]
            (ntmLeftVar M x t (s+1) 0) write]
      rw [show ntmCNFWeight
          (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
            M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = 9 by
        simpa [ntmSetRightCell] using
          ntmSetSymbol_weight [ntmNeg (ntmChoiceVar M x t s q a j)]
            (ntmRightVar M x t (s+1) (ntmRadius x t - 1)) M.machine.blank]
      nlinarith


theorem ntmIndexedTransitions_length
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction)) :
    (ntmIndexedTransitions ts).length = ts.length := by
  unfold ntmIndexedTransitions
  generalize hstart : 0 = start
  subst start
  induction ts with
  | nil => rfl
  | cons tr rest ih =>
      simp [ntmIndexedTransitionsAux, ih]

theorem ntmGuardChoiceClause_weight
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    ntmClauseWeight (ntmGuardChoiceClause M x t s q a) =
      (M.machine.transition q a).length + 3 := by
  simp [ntmGuardChoiceClause, ntmClauseWeight, ntmIndexedTransitions_length]

theorem ntmChoiceGuard_weight
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) (j : Nat) :
    ntmCNFWeight (ntmChoiceGuardCNF M x t s q a j) = 6 := by
  simp [ntmChoiceGuardCNF, ntmCNFWeight, ntmClauseWeight]

theorem ntmAtMostOne_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    ntmCNFWeight (ntmAtMostOneChoiceCNF M x t s q a) <=
      3 * (M.machine.transition q a).length ^ 2 := by
  let ids := (ntmIndexedTransitions (M.machine.transition q a)).map Prod.fst
  unfold ntmAtMostOneChoiceCNF
  have houter := ntmCNFWeight_flatMap_list_le ids
    (3 * ids.length)
    (fun j => ids.flatMap fun k =>
      if j < k then
        [[ntmNeg (ntmChoiceVar M x t s q a j),
          ntmNeg (ntmChoiceVar M x t s q a k)]]
      else [])
    (by
      intro j hj
      apply Nat.le_trans
        (ntmCNFWeight_flatMap_list_le ids 3
          (fun k =>
            if j < k then
              [[ntmNeg (ntmChoiceVar M x t s q a j),
                ntmNeg (ntmChoiceVar M x t s q a k)]]
            else [])
          (by
            intro k hk
            by_cases h : j < k
            · simp [h, ntmCNFWeight, ntmClauseWeight]
            · simp [h, ntmCNFWeight]))
      simp)
  have houter' :
      ntmCNFWeight
        (ids.flatMap fun j =>
          ids.flatMap fun k =>
            if j < k then
              [[ntmNeg (ntmChoiceVar M x t s q a j),
                ntmNeg (ntmChoiceVar M x t s q a k)]]
            else []) <=
        (M.machine.transition q a).length *
          (3 * (M.machine.transition q a).length) := by
    simpa [ids, ntmIndexedTransitions_length] using houter
  calc
    ntmCNFWeight
        (ids.flatMap fun j =>
          ids.flatMap fun k =>
            if j < k then
              [[ntmNeg (ntmChoiceVar M x t s q a j),
                ntmNeg (ntmChoiceVar M x t s q a k)]]
            else [])
        <= (M.machine.transition q a).length *
            (3 * (M.machine.transition q a).length) := houter'
    _ = 3 * (M.machine.transition q a).length ^ 2 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def ntmActiveChoiceWeightCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  3 +
  7 * ntmBranchBound M +
  3 * (ntmBranchBound M)^2 +
  ntmBranchBound M * ntmEffectWeightCap M x t

theorem ntmActiveChoice_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    ntmCNFWeight (ntmActiveChoiceCNF M x t s q a) <=
      ntmActiveChoiceWeightCap M x t := by
  let m := (M.machine.transition q a).length
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have hm : m <= ntmBranchBound M :=
    ntmBranchBound_ge_transition_length M q a
  have hfirst :
      ntmCNFWeight [ntmGuardChoiceClause M x t s q a] = m + 3 := by
    simp [ntmCNFWeight, ntmGuardChoiceClause_weight, m]
  have hguards :
      ntmCNFWeight
        (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
        <= m * 6 := by
    simpa [entries, m, ntmIndexedTransitions_length] using
      ntmCNFWeight_flatMap_list_le entries 6
        (fun p => ntmChoiceGuardCNF M x t s q a p.1)
        (by
          intro p hp
          simpa using ntmChoiceGuard_weight M x t s q a p.1)
  have hamo := ntmAtMostOne_weight_le M x t s q a
  have heffects :
      ntmCNFWeight
        (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))
        <= m * ntmEffectWeightCap M x t := by
    simpa [entries, m, ntmIndexedTransitions_length] using
      ntmCNFWeight_flatMap_list_le entries (ntmEffectWeightCap M x t)
        (fun p => ntmChoiceEffectCNF M x t s q a p)
        (by
          intro p hp
          exact ntmChoiceEffect_weight_le M x t s q a p)
  simp only [ntmActiveChoiceCNF, ntmCNFWeight_append]
  unfold ntmActiveChoiceWeightCap
  nlinarith [hm]

def ntmHaltedWeightCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  4 * ntmStateCount M + 30 + 60 * ntmRadius x t

def ntmTransitionCaseWeightCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmHaltedWeightCap M x t + ntmActiveChoiceWeightCap M x t

theorem ntmTransitionCase_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    ntmCNFWeight (ntmTransitionCaseCNF M x t s q a) <=
      ntmTransitionCaseWeightCap M x t := by
  unfold ntmTransitionCaseCNF ntmTransitionCaseWeightCap
  split
  · have h := ntmHaltedStutter_weight_le M x t s q a
    unfold ntmHaltedWeightCap
    omega
  · have h := ntmActiveChoice_weight_le M x t s q a
    omega

def ntmTransitionStepWeightCap
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmStateCount M * 3 * ntmTransitionCaseWeightCap M x t

theorem ntmTransitionStep_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) :
    ntmCNFWeight (ntmTransitionStepCNF M x t s) <=
      ntmTransitionStepWeightCap M x t := by
  unfold ntmTransitionStepCNF ntmTransitionStepWeightCap
  let qs := List.ofFn (fun q : Fin (M.stateCount + 1) => q)
  have hq :
      ntmCNFWeight
        (qs.flatMap (fun q =>
          ntmAlphabet.flatMap fun a =>
            ntmTransitionCaseCNF M x t s q a))
      <= qs.length * (3 * ntmTransitionCaseWeightCap M x t) := by
    apply ntmCNFWeight_flatMap_list_le
    intro q hqmem
    have ha := ntmCNFWeight_flatMap_list_le ntmAlphabet
      (ntmTransitionCaseWeightCap M x t)
      (fun a => ntmTransitionCaseCNF M x t s q a)
      (by
        intro a ha
        exact ntmTransitionCase_weight_le M x t s q a)
    simpa [ntmAlphabet] using ha
  simpa [qs, ntmStateCount] using hq

theorem ntmTransitions_weight_le
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmCNFWeight (ntmTransitionsCNF M x t) <=
      t * ntmTransitionStepWeightCap M x t := by
  unfold ntmTransitionsCNF
  exact ntmCNFWeight_flatMap_range_le t
    (ntmTransitionStepWeightCap M x t)
    (fun s => ntmTransitionStepCNF M x t s)
    (by
      intro s hs
      exact ntmTransitionStep_weight_le M x t s)


theorem ClauseVarsLe_nil
    (cap : Nat) :
    ClauseVarsLe cap [] := by
  intro l hl
  simp at hl

theorem ClauseVarsLe_singleton
    (cap : Nat) (l : NTMLiteral)
    (hl : l.var <= cap) :
    ClauseVarsLe cap [l] := by
  intro z hz
  simp at hz
  simpa [hz] using hl

theorem CNFVarsLe_nil
    (cap : Nat) :
    CNFVarsLe cap [] := by
  intro cl hcl
  simp at hcl

theorem CNFVarsLe_cons
    {cap : Nat} {cl : NTMClause} {f : NTMCNF}
    (hcl : ClauseVarsLe cap cl)
    (hf : CNFVarsLe cap f) :
    CNFVarsLe cap (cl :: f) := by
  intro c hc
  simp at hc
  rcases hc with rfl | hc
  · exact hcl
  · exact hf c hc

theorem ntmPos_var (v : Nat) : (ntmPos v).var = v := rfl
theorem ntmNeg_var (v : Nat) : (ntmNeg v).var = v := rfl

theorem ntmLitFor_var
    (v : Nat) (b : Bool) :
    (ntmLitFor v b).var = v := by
  cases b <;> rfl

theorem setState_varsLe
    (cap : Nat) (guard : NTMClause)
    (M : PolyNTMCandidate) (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (hg : ClauseVarsLe cap guard)
    (hv : forall q : Fin (M.stateCount + 1),
      ntmStateVar M t s q <= cap) :
    CNFVarsLe cap (ntmSetStateClauses guard M t s target) := by
  intro cl hcl
  unfold ntmSetStateClauses at hcl
  rw [List.mem_ofFn] at hcl
  rcases hcl with ⟨q, rfl⟩
  apply ClauseVarsLe_append hg
  apply ClauseVarsLe_singleton
  simpa [ntmLitFor_var] using hv q

theorem setSymbol_varsLe
    (cap : Nat) (guard : NTMClause)
    (varAt : Option Bool -> Nat) (target : Option Bool)
    (hg : ClauseVarsLe cap guard)
    (hv : forall a : Option Bool, varAt a <= cap) :
    CNFVarsLe cap (ntmSetSymbolClauses guard varAt target) := by
  intro cl hcl
  unfold ntmSetSymbolClauses at hcl
  rw [List.mem_map] at hcl
  rcases hcl with ⟨a, ha, rfl⟩
  apply ClauseVarsLe_append hg
  apply ClauseVarsLe_singleton
  simpa [ntmLitFor_var] using hv a

theorem copySymbol_varsLe
    (cap : Nat) (guard : NTMClause)
    (oldVar newVar : Option Bool -> Nat)
    (hg : ClauseVarsLe cap guard)
    (hold : forall a, oldVar a <= cap)
    (hnew : forall a, newVar a <= cap) :
    CNFVarsLe cap (ntmCopySymbolClauses guard oldVar newVar) := by
  intro cl hcl
  unfold ntmCopySymbolClauses at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨a, ha, hcl⟩
  simp at hcl
  rcases hcl with rfl | rfl
  · apply ClauseVarsLe_append hg
    intro l hl
    simp at hl
    rcases hl with rfl | rfl
    · simpa using hold a
    · simpa using hnew a
  · apply ClauseVarsLe_append hg
    intro l hl
    simp at hl
    rcases hl with rfl | rfl
    · simpa using hold a
    · simpa using hnew a

theorem copyLeftAll_varsLe
    (cap : Nat) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (hs : s + 1 <= t)
    (hg : ClauseVarsLe cap guard)
    (hleft :
      forall u i a, u <= t -> i < ntmRadius x t ->
        ntmLeftVar M x t u i a <= cap) :
    CNFVarsLe cap (ntmCopyLeftAll guard M x t s) := by
  intro cl hcl
  unfold ntmCopyLeftAll at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨i, hi, hcl⟩
  have hir : i < ntmRadius x t := by
    simpa using List.mem_range.mp hi
  exact copySymbol_varsLe cap guard
    (ntmLeftVar M x t s i) (ntmLeftVar M x t (s+1) i)
    hg
    (fun a => hleft s i a (by omega) hir)
    (fun a => hleft (s+1) i a hs hir) cl hcl

theorem copyRightAll_varsLe
    (cap : Nat) (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (hs : s + 1 <= t)
    (hg : ClauseVarsLe cap guard)
    (hright :
      forall u i a, u <= t -> i < ntmRadius x t ->
        ntmRightVar M x t u i a <= cap) :
    CNFVarsLe cap (ntmCopyRightAll guard M x t s) := by
  intro cl hcl
  unfold ntmCopyRightAll at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨i, hi, hcl⟩
  have hir : i < ntmRadius x t := by
    simpa using List.mem_range.mp hi
  exact copySymbol_varsLe cap guard
    (ntmRightVar M x t s i) (ntmRightVar M x t (s+1) i)
    hg
    (fun a => hright s i a (by omega) hir)
    (fun a => hright (s+1) i a hs hir) cl hcl

theorem initial_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    CNFVarsLe (tableauVarCap M x t) (ntmInitialCNF M x t) := by
  unfold ntmInitialCNF
  apply CNFVarsLe_append
  · apply setState_varsLe
    · exact ClauseVarsLe_nil _
    · intro q
      exact Nat.le_of_lt (ntmStateVar_lt_tableauVarCap M x t 0 q (by omega))
  · apply CNFVarsLe_append
    · apply setSymbol_varsLe
      · exact ClauseVarsLe_nil _
      · intro a
        exact Nat.le_of_lt (ntmHeadVar_lt_tableauVarCap M x t 0 a (by omega))
    · apply CNFVarsLe_append
      · intro cl hcl
        rw [List.mem_flatMap] at hcl
        rcases hcl with ⟨i, hi, hcl⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        exact setSymbol_varsLe _ [] (ntmLeftVar M x t 0 i)
          ((inputTape x).left.getD i M.machine.blank)
          (ClauseVarsLe_nil _)
          (fun a => Nat.le_of_lt
            (ntmLeftVar_lt_tableauVarCap M x t 0 i a (by omega) hir))
          cl hcl
      · intro cl hcl
        rw [List.mem_flatMap] at hcl
        rcases hcl with ⟨i, hi, hcl⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        exact setSymbol_varsLe _ [] (ntmRightVar M x t 0 i)
          ((inputTape x).right.getD i M.machine.blank)
          (ClauseVarsLe_nil _)
          (fun a => Nat.le_of_lt
            (ntmRightVar_lt_tableauVarCap M x t 0 i a (by omega) hir))
          cl hcl

theorem filterMap_mem_exists
    {α β : Type} (f : α -> Option β) (xs : List α) (y : β)
    (hy : y ∈ xs.filterMap f) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs with
  | nil =>
      simp at hy
  | cons x xs ih =>
      simp only [List.filterMap_cons] at hy
      cases hfx : f x with
      | none =>
          simp [hfx] at hy
          rcases ih hy with ⟨z, hz, hfz⟩
          exact ⟨z, by simp [hz], hfz⟩
      | some z =>
          simp [hfx] at hy
          rcases hy with rfl | hy
          · exact ⟨x, by simp, hfx⟩
          · rcases ih hy with ⟨w, hw, hfw⟩
            exact ⟨w, by simp [hw], hfw⟩

theorem filterMap_length_le
    {α β : Type} (f : α -> Option β) (xs : List α) :
    (xs.filterMap f).length <= xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hfx : f x <;> simp [List.filterMap_cons, hfx, ih]

theorem final_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    CNFVarsLe (tableauVarCap M x t) (ntmFinalAcceptanceCNF M t) := by
  intro cl hcl
  simp [ntmFinalAcceptanceCNF] at hcl
  subst cl
  intro l hl
  unfold ntmAcceptingStateLits at hl
  rcases filterMap_mem_exists
      (fun q : Fin (M.stateCount + 1) =>
        if M.machine.accepting q = true then
          some (ntmPos (ntmStateVar M t t q))
        else none)
      (List.ofFn fun q : Fin (M.stateCount + 1) => q) l hl with
    ⟨q, hqmem, hq⟩
  by_cases hacc : M.machine.accepting q = true
  · simp [hacc] at hq
    subst l
    exact Nat.le_of_lt
      (ntmStateVar_lt_tableauVarCap M x t t q (by omega))
  · simp [hacc] at hq


theorem stateHeadGuard_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs : s <= t) :
    ClauseVarsLe (tableauVarCap M x t)
      [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)] := by
  intro l hl
  simp at hl
  rcases hl with rfl | rfl
  · simpa using Nat.le_of_lt
      (ntmStateVar_lt_tableauVarCap M x t s q hs)
  · simpa using Nat.le_of_lt
      (ntmHeadVar_lt_tableauVarCap M x t s a hs)

theorem choiceGuard_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) (j : Nat)
    (hs : s <= t) (hj : j <= ntmBranchBound M) :
    ClauseVarsLe (tableauVarCap M x t)
      [ntmNeg (ntmChoiceVar M x t s q a j)] := by
  intro l hl
  simp at hl
  subst l
  simpa using ntmChoiceVar_le_tableauVarCap M x t s q a j hs hj

theorem haltedStutter_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs : s < t) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmHaltedStutterCNF M x t s q a) := by
  let guard := [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  have hg := stateHeadGuard_varsLe M x t s q a (by omega)
  unfold ntmHaltedStutterCNF
  apply CNFVarsLe_append
  · apply setState_varsLe
    · exact hg
    · intro r
      exact Nat.le_of_lt
        (ntmStateVar_lt_tableauVarCap M x t (s+1) r (by omega))
  · apply CNFVarsLe_append
    · apply copySymbol_varsLe
      · exact hg
      · intro b
        exact Nat.le_of_lt
          (ntmHeadVar_lt_tableauVarCap M x t s b (by omega))
      · intro b
        exact Nat.le_of_lt
          (ntmHeadVar_lt_tableauVarCap M x t (s+1) b (by omega))
    · apply CNFVarsLe_append
      · exact copyLeftAll_varsLe _ guard M x t s (by omega) hg
          (by
            intro u i b hu hi
            exact Nat.le_of_lt
              (ntmLeftVar_lt_tableauVarCap M x t u i b hu hi))
      · exact copyRightAll_varsLe _ guard M x t s (by omega) hg
          (by
            intro u i b hu hi
            exact Nat.le_of_lt
              (ntmRightVar_lt_tableauVarCap M x t u i b hu hi))

theorem choiceGuardCNF_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) (j : Nat)
    (hs : s <= t) (hj : j <= ntmBranchBound M) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmChoiceGuardCNF M x t s q a j) := by
  have hc := ntmChoiceVar_le_tableauVarCap M x t s q a j hs hj
  have hsvar := Nat.le_of_lt (ntmStateVar_lt_tableauVarCap M x t s q hs)
  have hhvar := Nat.le_of_lt (ntmHeadVar_lt_tableauVarCap M x t s a hs)
  intro cl hcl
  simp [ntmChoiceGuardCNF] at hcl
  rcases hcl with rfl | rfl
  · intro l hl
    simp at hl
    rcases hl with rfl | rfl <;> simpa using hc <;> simpa using hsvar
  · intro l hl
    simp at hl
    rcases hl with rfl | rfl <;> simpa using hc <;> simpa using hhvar

theorem atMostOne_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs : s <= t) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmAtMostOneChoiceCNF M x t s q a) := by
  intro cl hcl
  unfold ntmAtMostOneChoiceCNF at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨j, hjmem, hcl⟩
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨k, hkmem, hcl⟩
  split at hcl
  · simp at hcl
    subst cl
    have hjEntry : ∃ tr, (j,tr) ∈ ntmIndexedTransitions (M.machine.transition q a) := by
      simpa using hjmem
    have hkEntry : ∃ tr, (k,tr) ∈ ntmIndexedTransitions (M.machine.transition q a) := by
      simpa using hkmem
    rcases hjEntry with ⟨trj,hjE⟩
    rcases hkEntry with ⟨trk,hkE⟩
    have hjlt := indexedTransitions_index_lt (M.machine.transition q a) hjE
    have hklt := indexedTransitions_index_lt (M.machine.transition q a) hkE
    have hjb := ntmBranchBound_ge_transition_length M q a
    intro l hl
    simp at hl
    rcases hl with rfl | rfl
    · simpa using ntmChoiceVar_le_tableauVarCap M x t s q a j hs (by omega)
    · simpa using ntmChoiceVar_le_tableauVarCap M x t s q a k hs (by omega)
  · simp at hcl

theorem choiceEffect_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (hs : s < t)
    (hj : entry.1 <= ntmBranchBound M) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmChoiceEffectCNF M x t s q a entry) := by
  let guard := [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
  have hg := choiceGuard_varsLe M x t s q a entry.1 (by omega) hj
  rcases entry with ⟨j, qNext, write, d⟩
  cases d with
  | stay =>
      simp only [ntmChoiceEffectCNF, ntmStayEffectCNF]
      apply CNFVarsLe_append
      · exact setState_varsLe _ guard M t (s + 1) qNext hg
          (fun r => Nat.le_of_lt
            (ntmStateVar_lt_tableauVarCap M x t (s + 1) r (by omega)))
      · apply CNFVarsLe_append
        · exact setSymbol_varsLe _ guard (ntmHeadVar M t (s + 1)) write hg
            (fun b => Nat.le_of_lt
              (ntmHeadVar_lt_tableauVarCap M x t (s + 1) b (by omega)))
        · apply CNFVarsLe_append
          · exact copyLeftAll_varsLe _ guard M x t s (by omega) hg
              (by
                intro u i b hu hi
                exact Nat.le_of_lt
                  (ntmLeftVar_lt_tableauVarCap M x t u i b hu hi))
          · exact copyRightAll_varsLe _ guard M x t s (by omega) hg
              (by
                intro u i b hu hi
                exact Nat.le_of_lt
                  (ntmRightVar_lt_tableauVarCap M x t u i b hu hi))
  | left =>
      simp only [ntmChoiceEffectCNF, ntmLeftEffectCNF]
      apply CNFVarsLe_append
      · exact setState_varsLe _ guard M t (s + 1) qNext hg
          (fun r => Nat.le_of_lt
            (ntmStateVar_lt_tableauVarCap M x t (s + 1) r (by omega)))
      · apply CNFVarsLe_append
        · exact copySymbol_varsLe _ guard
            (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)) hg
            (fun b => Nat.le_of_lt
              (ntmLeftVar_lt_tableauVarCap M x t s 0 b
                (by omega) (by simp [ntmRadius])))
            (fun b => Nat.le_of_lt
              (ntmHeadVar_lt_tableauVarCap M x t (s + 1) b (by omega)))
        · apply CNFVarsLe_append
          · intro cl hcl
            rw [List.mem_flatMap] at hcl
            rcases hcl with ⟨i, hi, hcl⟩
            have hir : i < ntmRadius x t - 1 := List.mem_range.mp hi
            exact copySymbol_varsLe _ guard
              (ntmLeftVar M x t s (i + 1))
              (ntmLeftVar M x t (s + 1) i) hg
              (fun b => Nat.le_of_lt
                (ntmLeftVar_lt_tableauVarCap M x t s (i + 1) b
                  (by omega) (by omega)))
              (fun b => Nat.le_of_lt
                (ntmLeftVar_lt_tableauVarCap M x t (s + 1) i b
                  (by omega) (by omega)))
              cl hcl
          · apply CNFVarsLe_append
            · exact setSymbol_varsLe _ guard
                (ntmLeftVar M x t (s + 1) (ntmRadius x t - 1))
                M.machine.blank hg
                (fun b => Nat.le_of_lt
                  (ntmLeftVar_lt_tableauVarCap M x t (s + 1)
                    (ntmRadius x t - 1) b
                    (by omega) (by simp [ntmRadius])))
            · apply CNFVarsLe_append
              · exact setSymbol_varsLe _ guard
                  (ntmRightVar M x t (s + 1) 0) write hg
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t (s + 1) 0 b
                      (by omega) (by simp [ntmRadius])))
              · intro cl hcl
                rw [List.mem_flatMap] at hcl
                rcases hcl with ⟨i, hi, hcl⟩
                have hir : i < ntmRadius x t - 1 := List.mem_range.mp hi
                exact copySymbol_varsLe _ guard
                  (ntmRightVar M x t s i)
                  (ntmRightVar M x t (s + 1) (i + 1)) hg
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t s i b
                      (by omega) (by omega)))
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t (s + 1) (i + 1) b
                      (by omega) (by omega)))
                  cl hcl
  | right =>
      simp only [ntmChoiceEffectCNF, ntmRightEffectCNF]
      apply CNFVarsLe_append
      · exact setState_varsLe _ guard M t (s + 1) qNext hg
          (fun r => Nat.le_of_lt
            (ntmStateVar_lt_tableauVarCap M x t (s + 1) r (by omega)))
      · apply CNFVarsLe_append
        · exact copySymbol_varsLe _ guard
            (ntmRightVar M x t s 0) (ntmHeadVar M t (s + 1)) hg
            (fun b => Nat.le_of_lt
              (ntmRightVar_lt_tableauVarCap M x t s 0 b
                (by omega) (by simp [ntmRadius])))
            (fun b => Nat.le_of_lt
              (ntmHeadVar_lt_tableauVarCap M x t (s + 1) b (by omega)))
        · apply CNFVarsLe_append
          · exact setSymbol_varsLe _ guard
              (ntmLeftVar M x t (s + 1) 0) write hg
              (fun b => Nat.le_of_lt
                (ntmLeftVar_lt_tableauVarCap M x t (s + 1) 0 b
                  (by omega) (by simp [ntmRadius])))
          · apply CNFVarsLe_append
            · intro cl hcl
              rw [List.mem_flatMap] at hcl
              rcases hcl with ⟨i, hi, hcl⟩
              have hir : i < ntmRadius x t - 1 := List.mem_range.mp hi
              exact copySymbol_varsLe _ guard
                (ntmLeftVar M x t s i)
                (ntmLeftVar M x t (s + 1) (i + 1)) hg
                (fun b => Nat.le_of_lt
                  (ntmLeftVar_lt_tableauVarCap M x t s i b
                    (by omega) (by omega)))
                (fun b => Nat.le_of_lt
                  (ntmLeftVar_lt_tableauVarCap M x t (s + 1) (i + 1) b
                    (by omega) (by omega)))
                cl hcl
            · apply CNFVarsLe_append
              · intro cl hcl
                rw [List.mem_flatMap] at hcl
                rcases hcl with ⟨i, hi, hcl⟩
                have hir : i < ntmRadius x t - 1 := List.mem_range.mp hi
                exact copySymbol_varsLe _ guard
                  (ntmRightVar M x t s (i + 1))
                  (ntmRightVar M x t (s + 1) i) hg
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t s (i + 1) b
                      (by omega) (by omega)))
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t (s + 1) i b
                      (by omega) (by omega)))
                  cl hcl
              · exact setSymbol_varsLe _ guard
                  (ntmRightVar M x t (s + 1) (ntmRadius x t - 1))
                  M.machine.blank hg
                  (fun b => Nat.le_of_lt
                    (ntmRightVar_lt_tableauVarCap M x t (s + 1)
                      (ntmRadius x t - 1) b
                      (by omega) (by simp [ntmRadius])))

theorem activeChoice_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs : s < t) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmActiveChoiceCNF M x t s q a) := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  simp only [ntmActiveChoiceCNF]
  apply CNFVarsLe_append
  · apply CNFVarsLe_cons
    · unfold ntmGuardChoiceClause
      apply ClauseVarsLe_append
      · exact stateHeadGuard_varsLe M x t s q a (by omega)
      · intro l hl
        rw [List.mem_map] at hl
        rcases hl with ⟨p,hp,rfl⟩
        have hpLt := indexedTransitions_index_lt (M.machine.transition q a)
          (by simpa [entries] using hp)
        have hb := ntmBranchBound_ge_transition_length M q a
        simpa using ntmChoiceVar_le_tableauVarCap M x t s q a p.1
          (by omega) (by omega)
    · exact CNFVarsLe_nil _
  · apply CNFVarsLe_append
    · intro cl hcl
      rw [List.mem_flatMap] at hcl
      rcases hcl with ⟨p,hp,hcl⟩
      have hpLt := indexedTransitions_index_lt (M.machine.transition q a)
        (by simpa [entries] using hp)
      have hb := ntmBranchBound_ge_transition_length M q a
      exact choiceGuardCNF_varsLe M x t s q a p.1
        (by omega) (by omega) cl hcl
    · apply CNFVarsLe_append
      · exact atMostOne_varsLe M x t s q a (by omega)
      · intro cl hcl
        rw [List.mem_flatMap] at hcl
        rcases hcl with ⟨p,hp,hcl⟩
        have hpLt := indexedTransitions_index_lt (M.machine.transition q a)
          (by simpa [entries] using hp)
        have hb := ntmBranchBound_ge_transition_length M q a
        exact choiceEffect_varsLe M x t s q a p hs (by omega) cl hcl

theorem transitionCase_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (hs : s < t) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmTransitionCaseCNF M x t s q a) := by
  unfold ntmTransitionCaseCNF
  split
  · exact haltedStutter_varsLe M x t s q a hs
  · exact activeChoice_varsLe M x t s q a hs

theorem transitionStep_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (hs : s < t) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmTransitionStepCNF M x t s) := by
  intro cl hcl
  unfold ntmTransitionStepCNF at hcl
  rw [List.mem_flatten] at hcl
  rcases hcl with ⟨f,hf,hcl⟩
  rw [List.mem_ofFn] at hf
  rcases hf with ⟨q,rfl⟩
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨a,ha,hcl⟩
  exact transitionCase_varsLe M x t s q a hs cl hcl

theorem transitions_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    CNFVarsLe (tableauVarCap M x t)
      (ntmTransitionsCNF M x t) := by
  intro cl hcl
  unfold ntmTransitionsCNF at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨s,hs,hcl⟩
  exact transitionStep_varsLe M x t s (List.mem_range.mp hs) cl hcl

theorem boundedExec_varsLe
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    CNFVarsLe (tableauVarCap M x t)
      (boundedExecTableauCNF_NTM M x t) := by
  unfold boundedExecTableauCNF_NTM
  apply CNFVarsLe_append
  · apply CNFVarsLe_append
    · exact initial_varsLe M x t
    · exact transitions_varsLe M x t
  · exact final_varsLe M x t

theorem boundedExec_maxVar_le
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmCNFMaxVar (boundedExecTableauCNF_NTM M x t) <=
      tableauVarCap M x t :=
  ntmCNFMaxVar_le_of_varsLe _ _ (boundedExec_varsLe M x t)


theorem ntmFinal_weight_le
    (M : PolyNTMCandidate) (t : Nat) :
    ntmCNFWeight (ntmFinalAcceptanceCNF M t) <=
      ntmStateCount M + 1 := by
  unfold ntmFinalAcceptanceCNF ntmAcceptingStateLits ntmCNFWeight ntmClauseWeight
  simp
  have hlen :
      ((List.ofFn fun q : Fin (M.stateCount + 1) => q).filterMap fun q =>
        if M.machine.accepting q = true then
          some (ntmPos (ntmStateVar M t t q))
        else none).length
      <= M.stateCount + 1 := by
    exact Nat.le_trans
      (filterMap_length_le
        (fun q : Fin (M.stateCount + 1) =>
          if M.machine.accepting q = true then
            some (ntmPos (ntmStateVar M t t q))
          else none)
        (List.ofFn fun q : Fin (M.stateCount + 1) => q))
      (by simp)
  simpa [ntmFinalAcceptanceCNF, ntmCNFWeight, ntmClauseWeight,
    ntmStateCount] using Nat.add_le_add_right hlen 1

def tableauCaseConst (M : PolyNTMCandidate) : Nat :=
  4 * ntmStateCount M + 30 +
  3 + 7 * ntmBranchBound M +
  3 * (ntmBranchBound M)^2 +
  ntmBranchBound M * (3 * ntmStateCount M + 50)

def tableauCaseLinear (M : PolyNTMCandidate) : Nat :=
  60 + 48 * ntmBranchBound M

theorem transitionCaseCap_linear
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmTransitionCaseWeightCap M x t =
      tableauCaseConst M +
      tableauCaseLinear M * ntmRadius x t := by
  unfold ntmTransitionCaseWeightCap ntmHaltedWeightCap
    ntmActiveChoiceWeightCap ntmEffectWeightCap
    tableauCaseConst tableauCaseLinear
  ring

def tableauWeightCoeff (M : PolyNTMCandidate) : Nat :=
  (2 * ntmStateCount M + 18) +
  (3 * ntmStateCount M *
    (tableauCaseConst M + tableauCaseLinear M)) +
  (ntmStateCount M + 1)

theorem boundedExec_weight_poly
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmCNFWeight (boundedExecTableauCNF_NTM M x t) <=
      tableauWeightCoeff M * (ntmRadius x t)^2 := by
  let r := ntmRadius x t
  let Q := ntmStateCount M
  let C := tableauCaseConst M
  let L := tableauCaseLinear M
  have hr : 1 <= r := by
    simp [r, ntmRadius]
  have ht : t <= r := by
    simp [r, ntmRadius]
    omega
  have hr_sq : r <= r^2 := by
    have h := Nat.mul_le_mul_left r hr
    simpa [pow_two, Nat.mul_comm] using h
  have hi0 :
      ntmCNFWeight (ntmInitialCNF M x t) <=
        2 * Q + 6 + 12 * r := by
    simpa [Q, r] using ntmInitial_weight_le M x t
  have hconst : 2 * Q + 6 <= (2 * Q + 6) * r := by
    have h := Nat.mul_le_mul_left (2 * Q + 6) hr
    simpa using h
  have hi' :
      ntmCNFWeight (ntmInitialCNF M x t) <=
        (2 * Q + 18) * r := by
    calc
      ntmCNFWeight (ntmInitialCNF M x t)
          <= 2 * Q + 6 + 12 * r := hi0
      _ <= (2 * Q + 6) * r + 12 * r :=
        Nat.add_le_add_right hconst (12 * r)
      _ = (2 * Q + 18) * r := by ring
  have hcase :
      ntmTransitionCaseWeightCap M x t = C + L * r := by
    simpa [C, L, r] using transitionCaseCap_linear M x t
  have hstep :
      ntmTransitionStepWeightCap M x t =
        Q * 3 * (C + L * r) := by
    simp [ntmTransitionStepWeightCap, hcase, Q]
  have hC : C <= C * r := by
    have h := Nat.mul_le_mul_left C hr
    simpa using h
  have hlin : C + L * r <= (C + L) * r := by
    calc
      C + L * r <= C * r + L * r :=
        Nat.add_le_add_right hC (L * r)
      _ = (C + L) * r := by ring
  have hstep_mono :
      Q * 3 * (C + L * r) <=
        Q * 3 * ((C + L) * r) :=
    Nat.mul_le_mul_left (Q * 3) hlin
  have htr0 := ntmTransitions_weight_le M x t
  rw [hstep] at htr0
  have htr_prod :
      t * (Q * 3 * (C + L * r)) <=
        r * (Q * 3 * ((C + L) * r)) :=
    Nat.mul_le_mul ht hstep_mono
  have htr' :
      ntmCNFWeight (ntmTransitionsCNF M x t) <=
        (3 * Q * (C + L)) * r^2 := by
    calc
      ntmCNFWeight (ntmTransitionsCNF M x t)
          <= t * (Q * 3 * (C + L * r)) := htr0
      _ <= r * (Q * 3 * ((C + L) * r)) := htr_prod
      _ = (3 * Q * (C + L)) * r^2 := by ring
  have hf0 := ntmFinal_weight_le M t
  have hfinal_const : Q <= Q * r := by
    have h := Nat.mul_le_mul_left Q hr
    simpa using h
  have hfinal_r : Q * r <= Q * r^2 :=
    Nat.mul_le_mul_left Q hr_sq
  have hf' :
      ntmCNFWeight (ntmFinalAcceptanceCNF M t) <= Q * r^2 := by
    calc
      ntmCNFWeight (ntmFinalAcceptanceCNF M t)
          <= Q := by simpa [Q] using hf0
      _ <= Q * r := hfinal_const
      _ <= Q * r^2 := hfinal_r
  have hi2 :
      ntmCNFWeight (ntmInitialCNF M x t) <=
        (2 * Q + 18) * r^2 :=
    Nat.le_trans hi' (Nat.mul_le_mul_left (2 * Q + 18) hr_sq)
  unfold boundedExecTableauCNF_NTM
  rw [ntmCNFWeight_append, ntmCNFWeight_append]
  change
    ntmCNFWeight (ntmInitialCNF M x t) +
        ntmCNFWeight (ntmTransitionsCNF M x t) +
        ntmCNFWeight (ntmFinalAcceptanceCNF M t) <=
      tableauWeightCoeff M * r^2
  have hsum :=
    Nat.add_le_add (Nat.add_le_add hi2 htr') hf'
  unfold tableauWeightCoeff
  simpa [Q, C, L, Nat.add_assoc, Nat.mul_add, Nat.add_mul] using hsum

def tableauVarCoeff (M : PolyNTMCandidate) : Nat :=
  (ntmStateCount M + 9) +
  ((3 * ntmStateCount M + 2) * (ntmBranchBound M + 1) +
    ntmBranchBound M) + 1

theorem tableauVarCap_poly
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    tableauVarCap M x t + 1 <=
      tableauVarCoeff M * (ntmRadius x t)^2 := by
  let r := ntmRadius x t
  let Q := ntmStateCount M
  let B := ntmBranchBound M
  have hr : 1 <= r := by simp [r, ntmRadius]
  have ht1 : t + 1 <= r := by
    simp [r, ntmRadius]
  have hr_sq : r <= r^2 := by
    have h := Nat.mul_le_mul_left r hr
    simpa [pow_two, Nat.mul_comm] using h
  have hQ : M.stateCount <= Q := by
    simp [Q, ntmStateCount]
  have hbase :
      ntmChoiceBase M x t <= (Q + 9) * r^2 := by
    unfold ntmChoiceBase ntmRightBase ntmLeftBase ntmHeadBase ntmStateSlots
    have hq := Nat.mul_le_mul_right Q ht1
    have h3 := Nat.mul_le_mul_right 3 ht1
    have h6r0 := Nat.mul_le_mul_right (r * 6) ht1
    have hq2 := Nat.le_trans hq (Nat.mul_le_mul_left Q hr_sq)
    have h32 := Nat.le_trans h3 (Nat.mul_le_mul_left 3 hr_sq)
    have h6r :
        (t + 1) * r * 6 <= 6 * r^2 := by
      calc
        (t + 1) * r * 6 <= r * r * 6 := by
          exact Nat.mul_le_mul_right 6 (Nat.mul_le_mul_right r ht1)
        _ = 6 * r^2 := by ring
    simp [Q, r]
    calc
      (t + 1) * Q + (t + 1) * 3 +
          (t + 1) * r * 3 + (t + 1) * r * 3
          <= Q * r^2 + 3 * r^2 + 6 * r^2 := by
            omega
      _ = (Q + 9) * r^2 := by ring
  have hsq : t * Q + M.stateCount <= r * Q := by
    calc
      t * Q + M.stateCount <= t * Q + Q :=
        Nat.add_le_add_left hQ (t * Q)
      _ = (t + 1) * Q := by ring
      _ <= r * Q := Nat.mul_le_mul_right Q ht1
  have hthree :
      (t * Q + M.stateCount) * 3 + 2 <=
        (3 * Q + 2) * r := by
    have hmul3 := Nat.mul_le_mul_right 3 hsq
    have htwo : 2 <= 2 * r := by
      have h := Nat.mul_le_mul_left 2 hr
      simpa using h
    calc
      (t * Q + M.stateCount) * 3 + 2
          <= (r * Q) * 3 + 2 * r :=
            Nat.add_le_add hmul3 htwo
      _ = (3 * Q + 2) * r := by ring
  have hmulB :=
    Nat.mul_le_mul_right (B + 1) hthree
  have hB : B <= B * r := by
    have h := Nat.mul_le_mul_left B hr
    simpa using h
  have hinner :
      (((t * Q + M.stateCount) * 3 + 2) * (B + 1) + B)
      <= (((3 * Q + 2) * (B + 1) + B) * r) := by
    calc
      (((t * Q + M.stateCount) * 3 + 2) * (B + 1) + B)
          <= (((3 * Q + 2) * r) * (B + 1) + B * r) :=
            Nat.add_le_add hmulB hB
      _ = (((3 * Q + 2) * (B + 1) + B) * r) := by ring
  have hinner2 :
      (((t * Q + M.stateCount) * 3 + 2) * (B + 1) + B)
      <= (((3 * Q + 2) * (B + 1) + B) * r^2) :=
    Nat.le_trans hinner
      (Nat.mul_le_mul_left
        (((3 * Q + 2) * (B + 1) + B)) hr_sq)
  have hone : 1 <= r^2 := by
    have hp : 0 < r^2 := by positivity
    omega
  have hsum :=
    Nat.add_le_add
      (Nat.add_le_add hbase hinner2)
      hone
  unfold tableauVarCap tableauVarCoeff
  simpa [Q, B, r, Nat.add_assoc, Nat.mul_add, Nat.add_mul] using hsum

theorem boundedExec_maxVar_poly
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ntmCNFMaxVar (boundedExecTableauCNF_NTM M x t) + 1 <=
      tableauVarCoeff M * (ntmRadius x t)^2 := by
  have hmax := boundedExec_maxVar_le M x t
  have hcap := tableauVarCap_poly M x t
  omega

def tableauEncodingCoeff (M : PolyNTMCandidate) : Nat :=
  16 * tableauWeightCoeff M * tableauVarCoeff M + 3

theorem boundedExec_encoded_length_poly
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    (encodeCircuit (boundedExecCircuit_NTM M x t)).length <=
      tableauEncodingCoeff M * (x.length + t + 1)^4 := by
  let f := boundedExecTableauCNF_NTM M x t
  let r := ntmRadius x t
  let W := tableauWeightCoeff M
  let V := tableauVarCoeff M
  have hr : 1 <= r := by simp [r, ntmRadius]
  have hr4 : 1 <= r^4 := by
    have hp : 0 < r^4 := by positivity
    omega
  have hw :
      ntmCNFWeight f <= W * r^2 := by
    simpa [f, W, r] using boundedExec_weight_poly M x t
  have hv :
      ntmCNFMaxVar f + 1 <= V * r^2 := by
    simpa [f, V, r] using boundedExec_maxVar_poly M x t
  have henc := ntmCNFCircuit_encoding_le f
  have hmul1 :
      13 * ntmCNFWeight f <= 13 * (W * r^2) :=
    Nat.mul_le_mul_left 13 hw
  have hmul2 :
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1) <=
        13 * (W * r^2) * (V * r^2) :=
    Nat.mul_le_mul hmul1 hv
  have h13 : 13 * W * V <= 16 * W * V := by
    exact Nat.mul_le_mul_right (W * V) (by omega)
  have hprod :
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1) <=
        16 * W * V * r^4 := by
    calc
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1)
          <= 13 * (W * r^2) * (V * r^2) := hmul2
      _ = (13 * W * V) * r^4 := by ring
      _ <= (16 * W * V) * r^4 :=
        Nat.mul_le_mul_right (r^4) h13
  have hthree : 3 <= 3 * r^4 := by
    have h := Nat.mul_le_mul_left 3 hr4
    simpa using h
  have hmain :
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1) + 3 <=
        (16 * W * V + 3) * r^4 := by
    calc
      13 * ntmCNFWeight f * (ntmCNFMaxVar f + 1) + 3
          <= 16 * W * V * r^4 + 3 * r^4 :=
            Nat.add_le_add hprod hthree
      _ = (16 * W * V + 3) * r^4 := by ring
  have hcirc :
      boundedExecCircuit_NTM M x t = ntmCNFCircuit f := by
    rfl
  rw [hcirc]
  exact Nat.le_trans henc (by
    simpa [tableauEncodingCoeff, W, V, f, r, ntmRadius] using hmain)

theorem boundedExec_initial_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    evalNTMCNF sigma (ntmInitialCNF M x t) = true := by
  have h :=
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)).mp
      (by simpa [boundedExecTableauCNF_NTM, List.append_assoc] using hSat)
  exact h.1

theorem ntmInitial_state_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall q : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t 0 q) = decide (q = M.machine.initial) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have hparts :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetLeftCell [] M x t 0 i
            ((inputTape x).left.getD i M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  exact (eval_ntmSetStateClauses_nil_iff
    sigma M t 0 M.machine.initial).mp hparts.1

theorem ntmInitial_state_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    ExistsUnique (fun q : Fin (M.stateCount + 1) =>
      sigma (ntmStateVar M t 0 q) = true) := by
  refine ⟨M.machine.initial, ?_, ?_⟩
  · simpa using
      ntmInitial_state_exact M x t sigma hSat M.machine.initial
  · intro q hq
    have hExact := ntmInitial_state_exact M x t sigma hSat q
    have hdec : decide (q = M.machine.initial) = true := by
      simpa [hq] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_head_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall a : Option Bool,
      sigma (ntmHeadVar M t 0 a) =
        decide (a = (inputTape x).head) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetLeftCell [] M x t 0 i
            ((inputTape x).left.getD i M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  exact (eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmHeadVar M t 0) (inputTape x).head).mp h2.1

theorem ntmInitial_head_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    ExistsUnique (fun a : Option Bool =>
      sigma (ntmHeadVar M t 0 a) = true) := by
  refine ⟨(inputTape x).head, ?_, ?_⟩
  · simpa using
      ntmInitial_head_exact M x t sigma hSat (inputTape x).head
  · intro a ha
    have hExact := ntmInitial_head_exact M x t sigma hSat a
    have hdec : decide (a = (inputTape x).head) = true := by
      simpa [ha] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_left_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t 0 i b) =
        decide (b = (inputTape x).left.getD i M.machine.blank) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetLeftCell [] M x t 0 j
            ((inputTape x).left.getD j M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetRightCell [] M x t 0 j
            ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)))
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp h2.2
  have hiSat :=
    (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
      (fun j => ntmSetLeftCell [] M x t 0 j
        ((inputTape x).left.getD j M.machine.blank))).mp h3.1 i hi
  exact (eval_ntmSetLeftCell_nil_iff M x t sigma i
    ((inputTape x).left.getD i M.machine.blank)).mp hiSat

theorem ntmInitial_left_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    ExistsUnique (fun b : Option Bool =>
      sigma (ntmLeftVar M x t 0 i b) = true) := by
  let target := (inputTape x).left.getD i M.machine.blank
  refine ⟨target, ?_, ?_⟩
  · simpa [target] using
      ntmInitial_left_exact M x t sigma hSat i hi target
  · intro b hb
    have hExact := ntmInitial_left_exact M x t sigma hSat i hi b
    have hdec : decide (b = target) = true := by
      simpa [target, hb] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_right_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t 0 i b) =
        decide (b = (inputTape x).right.getD i M.machine.blank) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetLeftCell [] M x t 0 j
            ((inputTape x).left.getD j M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetRightCell [] M x t 0 j
            ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)))
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp h2.2
  have hiSat :=
    (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
      (fun j => ntmSetRightCell [] M x t 0 j
        ((inputTape x).right.getD j M.machine.blank))).mp h3.2 i hi
  exact (eval_ntmSetRightCell_nil_iff M x t sigma i
    ((inputTape x).right.getD i M.machine.blank)).mp hiSat

theorem ntmInitial_right_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    ExistsUnique (fun b : Option Bool =>
      sigma (ntmRightVar M x t 0 i b) = true) := by
  let target := (inputTape x).right.getD i M.machine.blank
  refine ⟨target, ?_, ?_⟩
  · simpa [target] using
      ntmInitial_right_exact M x t sigma hSat i hi target
  · intro b hb
    have hExact := ntmInitial_right_exact M x t sigma hSat i hi b
    have hdec : decide (b = target) = true := by
      simpa [target, hb] using hExact.symm
    exact of_decide_eq_true hdec

end PNPNTMTableauEncoding
end Real
end MCore
