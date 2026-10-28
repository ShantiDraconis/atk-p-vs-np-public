import MCore.Real.P02ComplementRunRealization

namespace MCore
namespace Real
namespace SourceRecovery

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open PNPNTMTableauEncoding
open PNPNTMTableauFrontier
open PNPNTMTableauClosure

/-- Inverse of the literal encoding used by the concrete NTM tableau. -/
def decodeNTMLiteral : Circuit → Option NTMLiteral
  | .input v => some (ntmPos v)
  | .not (.input v) => some (ntmNeg v)
  | _ => none

/-- Inverse of the right-associated clause AST emitted by ntmClauseCircuit. -/
def decodeNTMClause : Circuit → Option NTMClause
  | .const false => some []
  | .or a rest =>
      match decodeNTMLiteral a, decodeNTMClause rest with
      | some l, some ls => some (l :: ls)
      | _, _ => none
  | _ => none

/-- Inverse of ntmCNFCircuit on its range. -/
def decodeNTMCNF : Circuit → Option NTMCNF
  | .const true => some []
  | .and c rest =>
      match decodeNTMClause c, decodeNTMCNF rest with
      | some cl, some cs => some (cl :: cs)
      | _, _ => none
  | _ => none

@[simp] theorem decodeNTMLiteral_ntmLiteralCircuit
    (l : NTMLiteral) :
    decodeNTMLiteral (ntmLiteralCircuit l) = some l := by
  cases l with
  | mk v positive =>
      cases positive <;>
        rfl

@[simp] theorem decodeNTMClause_ntmClauseCircuit
    (c : NTMClause) :
    decodeNTMClause (ntmClauseCircuit c) = some c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      simp [ntmClauseCircuit, decodeNTMClause, ih]

@[simp] theorem decodeNTMCNF_ntmCNFCircuit
    (F : NTMCNF) :
    decodeNTMCNF (ntmCNFCircuit F) = some F := by
  induction F with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [ntmCNFCircuit, decodeNTMCNF, ih]

/-- The reduction really encodes the concrete complemented NTM tableau. -/
theorem decodeCircuit_reduce
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeCircuit ((complementSemanticReduction M hTotal).reduce x) =
      some
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM
            (complementToNTMCandidate M)
            x
            (M.timeBound x.length))) := by
  simpa [complementSemanticReduction,
    PNPNTMTableauFrontier.NTMTableauProducer.toSemanticReduction,
    PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    P02ComplementRunRealization.complementRunRealization,
    boundedExecCircuit_NTM] using
      (decodeCircuit_encode
        (boundedExecCircuit_NTM
          (complementToNTMCandidate M)
          x
          (M.timeBound x.length)))

theorem ntmRadius_eq_of_length_eq
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmRadius x t = ntmRadius y t := by
  simp [ntmRadius, h]

theorem ntmRightBase_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmRightBase M x t = ntmRightBase M y t := by
  simp [ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmChoiceBase_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmChoiceBase M x t = ntmChoiceBase M y t := by
  simp [ntmChoiceBase, ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmLeftVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s i : Nat}
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmLeftVar M x t s i a = ntmLeftVar M y t s i a := by
  simp [ntmLeftVar, ntmLeftBase, ntmRadius, h]

theorem ntmRightVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s i : Nat}
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmRightVar M x t s i a = ntmRightVar M y t s i a := by
  simp [ntmRightVar, ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmChoiceVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s j : Nat}
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmChoiceVar M x t s q a j = ntmChoiceVar M y t s q a j := by
  simp [ntmChoiceVar, ntmChoiceBase, ntmRightBase, ntmLeftBase, ntmRadius, h]

/-- The canonical input tape representation itself loses no source bits. -/
theorem inputTape_injective :
    Function.Injective inputTape := by
  intro x y h
  cases x with
  | nil =>
      cases y with
      | nil => rfl
      | cons b bs =>
          simp [inputTape] at h
  | cons a as =>
      cases y with
      | nil =>
          simp [inputTape] at h
      | cons b bs =>
          simp [inputTape] at h
          rcases h with ⟨hab, htail⟩
          subst b
          have : as = bs := by
            simpa using htail
          subst bs
          rfl

/-- Canonical dummy input used only to recover length-dependent variable IDs. -/
def layoutInput (n : Nat) : BitString :=
  List.replicate n false

@[simp] theorem layoutInput_length (n : Nat) :
    (layoutInput n).length = n := by
  simp [layoutInput]

/--
Decode exactly one three-clause symbol block produced by ntmSetSymbolClauses.
This is positional: it never searches the full CNF.
-/
def decodeSymbolBlock
    (varAt : Option Bool → Nat)
    (block : NTMCNF) : Option (Option Bool) :=
  if block = ntmSetSymbolClauses [] varAt none then
    some none
  else if block = ntmSetSymbolClauses [] varAt (some false) then
    some (some false)
  else if block = ntmSetSymbolClauses [] varAt (some true) then
    some (some true)
  else
    none

@[simp] theorem decodeSymbolBlock_setSymbolClauses
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    decodeSymbolBlock varAt (ntmSetSymbolClauses [] varAt target) =
      some target := by
  cases target with
  | none =>
      simp [decodeSymbolBlock]
  | some b =>
      cases b <;>
        simp [decodeSymbolBlock, ntmSetSymbolClauses, ntmAlphabet,
          ntmLitFor, ntmPos, ntmNeg]

def initialStateClauseCount (M : PolyNTMCandidate) : Nat :=
  ntmStateCount M

def retainedRadius (n t : Nat) : Nat :=
  n + t + 1

def headBlockOffset (M : PolyNTMCandidate) : Nat :=
  initialStateClauseCount M

def rightBlockOffset
    (M : PolyNTMCandidate)
    (n t : Nat) : Nat :=
  initialStateClauseCount M + 3 + 3 * retainedRadius n t

def symbolBlockAt
    (F : NTMCNF)
    (offset : Nat) : NTMCNF :=
  (F.drop offset).take 3

def getHeadAt0
    (M : PolyNTMCandidate)
    (t : Nat)
    (F : NTMCNF) : Option (Option Bool) :=
  decodeSymbolBlock
    (ntmHeadVar M t 0)
    (symbolBlockAt F (headBlockOffset M))

def getRightAt0
    (M : PolyNTMCandidate)
    (n t : Nat)
    (F : NTMCNF)
    (i : Nat) : Option (Option Bool) :=
  decodeSymbolBlock
    (ntmRightVar M (layoutInput n) t 0 i)
    (symbolBlockAt F (rightBlockOffset M n t + 3 * i))

/-- Read exactly the requested number of source-tail cells. -/
def readRightBits
    (M : PolyNTMCandidate)
    (n t : Nat)
    (F : NTMCNF) :
    Nat → Nat → Option BitString
  | _, 0 => some []
  | i, count + 1 =>
      match getRightAt0 M n t F i with
      | some (some b) =>
          match readRightBits M n t F (i + 1) count with
          | some bs => some (b :: bs)
          | none => none
      | _ => none

/--
Operational inverse of the time-0 source encoding.
For n=0 the head must be blank. For n+1 the head contains the first bit and
the following n bits are read from right(0,0),...,right(0,n-1).
-/
def extractInitialTape
    (M : PolyNTMCandidate)
    (n t : Nat)
    (F : NTMCNF) : Option BitString :=
  match n with
  | 0 =>
      match getHeadAt0 M t F with
      | some none => some []
      | _ => none
  | k + 1 =>
      match getHeadAt0 M t F with
      | some (some b) =>
          match readRightBits M n t F 0 k with
          | some bs => some (b :: bs)
          | none => none
      | _ => none

@[simp] theorem length_ntmSetStateClauses
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    (ntmSetStateClauses [] M t s target).length = ntmStateCount M := by
  simp [ntmSetStateClauses, ntmStateCount]

@[simp] theorem length_ntmSetSymbolClauses
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    (ntmSetSymbolClauses [] varAt target).length = 3 := by
  simp [ntmSetSymbolClauses, ntmAlphabet]

@[simp] theorem length_initial_left_block
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ((List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetLeftCell [] M x t 0 i
        ((inputTape x).left.getD i M.machine.blank))).length =
      3 * ntmRadius x t := by
  simp [ntmSetLeftCell, length_ntmSetSymbolClauses, Nat.mul_comm]

@[simp] theorem length_initial_right_block
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ((List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank))).length =
      3 * ntmRadius x t := by
  simp [ntmSetRightCell, length_ntmSetSymbolClauses, Nat.mul_comm]

/--
The retained offset is exactly the number of clauses preceding the initial
right-tape block.
-/
theorem rightBlockOffset_eq_prefix_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    rightBlockOffset M x.length t =
      (ntmSetStateClauses [] M t 0 M.machine.initial).length +
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head).length +
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank))).length := by
  simp [rightBlockOffset, initialStateClauseCount, retainedRadius,
    ntmRadius, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
The head offset is exactly the number of clauses preceding the initial head
symbol block.
-/
theorem headBlockOffset_eq_prefix_length
    (M : PolyNTMCandidate)
    (t : Nat) :
    headBlockOffset M =
      (ntmSetStateClauses [] M t 0 M.machine.initial).length := by
  simp [headBlockOffset, initialStateClauseCount]

/-- Slicing at the retained head offset recovers exactly the three head clauses. -/
theorem drop_headBlockOffset_take_head
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    symbolBlockAt (ntmInitialCNF M x t) (headBlockOffset M) =
      ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head := by
  unfold symbolBlockAt ntmInitialCNF
  rw [headBlockOffset_eq_prefix_length]
  simp [length_ntmSetSymbolClauses]

/--
Uniform three-clause blocks in a range-flatMap can be recovered by their
block index. This is the only generic list-arithmetic lemma needed by the
time-zero right-tape decoder.
-/
theorem flatMap_range_block_slice
    (f : Nat → NTMCNF)
    (h3 : ∀ i, (f i).length = 3)
    (k i : Nat)
    (hi : i < k) :
    (((List.range k).flatMap f).drop (3 * i)).take 3 = f i := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append]
      by_cases hik : i < k
      · have hlen :
          ((List.range k).flatMap f).length = 3 * k := by
            simp [h3, Nat.mul_comm]
        have hfit : 3 * i + 3 ≤ ((List.range k).flatMap f).length := by
          rw [hlen]
          omega
        rw [List.drop_append_of_le]
        · rw [List.take_append_of_le]
          · exact ih i hik
          · simpa [List.length_drop, hlen] using hfit
        · rw [hlen]
          omega
      · have hikEq : i = k := by omega
        subst i
        have hlen :
          ((List.range k).flatMap f).length = 3 * k := by
            simp [h3, Nat.mul_comm]
        rw [List.drop_append]
        simp [hlen, h3]

/-- Slicing the concrete right block at cell i recovers exactly that cell block. -/
theorem drop_rightBlockOffset_take_right
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    symbolBlockAt
        (ntmInitialCNF M x t)
        (rightBlockOffset M x.length t + 3 * i) =
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank) := by
  unfold symbolBlockAt ntmInitialCNF
  let stateBlock :=
    ntmSetStateClauses [] M t 0 M.machine.initial
  let headBlock :=
    ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head
  let leftBlock :=
    (List.range (ntmRadius x t)).flatMap (fun j =>
      ntmSetLeftCell [] M x t 0 j
        ((inputTape x).left.getD j M.machine.blank))
  let rightCell : Nat → NTMCNF := fun j =>
    ntmSetRightCell [] M x t 0 j
      ((inputTape x).right.getD j M.machine.blank)
  have hoff :
      rightBlockOffset M x.length t =
        stateBlock.length + headBlock.length + leftBlock.length := by
    simpa [stateBlock, headBlock, leftBlock] using
      rightBlockOffset_eq_prefix_length M x t
  rw [hoff]
  simp only [List.append_assoc]
  rw [List.drop_append_of_le]
  · rw [List.drop_append_of_le]
    · rw [List.drop_append_of_le]
      · simpa [rightCell] using
          flatMap_range_block_slice rightCell
            (fun j => by
              simp [rightCell, ntmSetRightCell,
                length_ntmSetSymbolClauses])
            (ntmRadius x t) i hi
      · simp
    · simp
  · simp

@[simp] theorem getHeadAt0_initialCNF
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    getHeadAt0 M t (ntmInitialCNF M x t) = some (inputTape x).head := by
  simp [getHeadAt0, drop_headBlockOffset_take_head]

@[simp] theorem getRightAt0_initialCNF
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    getRightAt0 M x.length t (ntmInitialCNF M x t) i =
      some ((inputTape x).right.getD i M.machine.blank) := by
  have hlayout :
      ntmRightVar M (layoutInput x.length) t 0 i =
        ntmRightVar M x t 0 i := by
    apply ntmRightVar_eq_of_length_eq
    simp
  simp [getRightAt0, drop_rightBlockOffset_take_right,
    hi, ntmSetRightCell, hlayout]

/-- Pure list model of the operational right-tape reader. -/
def getDBits (bs : BitString) : Nat → Nat → BitString
  | _, 0 => []
  | i, count + 1 =>
      bs.getD i false :: getDBits bs (i + 1) count

theorem map_some_getD_of_lt
    (bs : BitString)
    (i : Nat)
    (hi : i < bs.length) :
    (bs.map some).getD i none = some (bs.getD i false) := by
  induction bs generalizing i with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          simp [List.getD_cons_zero]
      | succ i =>
          have hi' : i < bs.length := by
            simpa using hi
          simpa [List.getD_cons_succ] using ih i hi'

theorem getDBits_cons_succ
    (b : Bool)
    (bs : BitString)
    (i count : Nat) :
    getDBits (b :: bs) (i + 1) count =
      getDBits bs i count := by
  induction count generalizing i with
  | zero =>
      rfl
  | succ count ih =>
      simp [getDBits, List.getD_cons_succ, ih, Nat.add_assoc]

@[simp] theorem getDBits_all
    (bs : BitString) :
    getDBits bs 0 bs.length = bs := by
  induction bs with
  | nil =>
      rfl
  | cons b bs ih =>
      simp [getDBits, getDBits_cons_succ, ih, List.getD_cons_zero]

/--
The operational reader agrees with the pure getD model on every in-range
segment of the source tail.
-/
theorem readRightBits_initialCNF_aux
    (M : PolyNTMCandidate)
    (b : Bool)
    (bs : BitString)
    (t i count : Nat)
    (hspan : i + count ≤ bs.length) :
    readRightBits M (b :: bs).length t
        (ntmInitialCNF M (b :: bs) t) i count =
      some (getDBits bs i count) := by
  induction count generalizing i with
  | zero =>
      rfl
  | succ count ih =>
      have hi : i < bs.length := by
        omega
      have hRadius : i < ntmRadius (b :: bs) t := by
        simp [ntmRadius]
        omega
      have hget :
          getRightAt0 M (b :: bs).length t
              (ntmInitialCNF M (b :: bs) t) i =
            some (some (bs.getD i false)) := by
        rw [getRightAt0_initialCNF M (b :: bs) t i hRadius]
        simp [inputTape, M.blank_none, map_some_getD_of_lt bs i hi]
      rw [readRightBits]
      rw [hget]
      have hspan' : (i + 1) + count ≤ bs.length := by
        omega
      rw [ih (i + 1) hspan']
      rfl

@[simp] theorem readRightBits_initialCNF
    (M : PolyNTMCandidate)
    (b : Bool)
    (bs : BitString)
    (t : Nat) :
    readRightBits M (b :: bs).length t
        (ntmInitialCNF M (b :: bs) t) 0 bs.length =
      some bs := by
  rw [readRightBits_initialCNF_aux M b bs t 0 bs.length]
  · simp
  · simp

/-- The positional time-zero decoder is a left inverse of ntmInitialCNF. -/
@[simp] theorem extractInitialTape_initialCNF
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    extractInitialTape M x.length t (ntmInitialCNF M x t) = some x := by
  cases x with
  | nil =>
      simp [extractInitialTape, getHeadAt0_initialCNF, inputTape]
  | cons b bs =>
      simp [extractInitialTape, getHeadAt0_initialCNF,
        readRightBits_initialCNF, inputTape]

/--
Decode a source from a circuit known to carry the concrete tableau shape,
using retained source length and clock metadata.
-/
def decodeSource
    (M : PolyNTMCandidate)
    (n t : Nat)
    (c : Circuit) : Option BitString :=
  match decodeNTMCNF c with
  | none => none
  | some F => extractInitialTape M n t F

@[simp] theorem decodeSource_ntmCNFCircuit_initial
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    decodeSource M x.length t
        (ntmCNFCircuit (ntmInitialCNF M x t)) =
      some x := by
  simp [decodeSource]

/-- A three-clause slice wholly contained in a prefix is unchanged by appending. -/
theorem symbolBlockAt_append_left
    (F G : NTMCNF)
    (offset : Nat)
    (hfit : offset + 3 ≤ F.length) :
    symbolBlockAt (F ++ G) offset = symbolBlockAt F offset := by
  unfold symbolBlockAt
  rw [List.drop_append_of_le]
  · rw [List.take_append_of_le]
    · rfl
    · simpa [List.length_drop] using hfit
  · omega

theorem head_slice_fits_initial
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    headBlockOffset M + 3 ≤ (ntmInitialCNF M x t).length := by
  unfold ntmInitialCNF
  rw [headBlockOffset_eq_prefix_length]
  simp [length_ntmSetSymbolClauses]

theorem right_slice_fits_initial
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    rightBlockOffset M x.length t + 3 * i + 3 ≤
      (ntmInitialCNF M x t).length := by
  unfold ntmInitialCNF
  rw [rightBlockOffset_eq_prefix_length]
  simp [length_initial_right_block]
  omega

@[simp] theorem getHeadAt0_boundedExecTableau
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    getHeadAt0 M t (boundedExecTableauCNF_NTM M x t) =
      some (inputTape x).head := by
  unfold boundedExecTableauCNF_NTM
  have hslice :
      symbolBlockAt
          (ntmInitialCNF M x t ++
            (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t))
          (headBlockOffset M) =
        symbolBlockAt (ntmInitialCNF M x t) (headBlockOffset M) := by
    exact symbolBlockAt_append_left _ _ _
      (head_slice_fits_initial M x t)
  simp [getHeadAt0, hslice, drop_headBlockOffset_take_head]

@[simp] theorem getRightAt0_boundedExecTableau
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    getRightAt0 M x.length t
        (boundedExecTableauCNF_NTM M x t) i =
      some ((inputTape x).right.getD i M.machine.blank) := by
  unfold boundedExecTableauCNF_NTM
  have hslice :
      symbolBlockAt
          (ntmInitialCNF M x t ++
            (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t))
          (rightBlockOffset M x.length t + 3 * i) =
        symbolBlockAt
          (ntmInitialCNF M x t)
          (rightBlockOffset M x.length t + 3 * i) := by
    exact symbolBlockAt_append_left _ _ _
      (right_slice_fits_initial M x t i hi)
  have hlayout :
      ntmRightVar M (layoutInput x.length) t 0 i =
        ntmRightVar M x t 0 i := by
    apply ntmRightVar_eq_of_length_eq
    simp
  simp [getRightAt0, hslice, drop_rightBlockOffset_take_right,
    hi, ntmSetRightCell, hlayout]

theorem readRightBits_boundedExec_aux
    (M : PolyNTMCandidate)
    (b : Bool)
    (bs : BitString)
    (t i count : Nat)
    (hspan : i + count ≤ bs.length) :
    readRightBits M (b :: bs).length t
        (boundedExecTableauCNF_NTM M (b :: bs) t) i count =
      some (getDBits bs i count) := by
  induction count generalizing i with
  | zero =>
      rfl
  | succ count ih =>
      have hi : i < bs.length := by omega
      have hRadius : i < ntmRadius (b :: bs) t := by
        simp [ntmRadius]
        omega
      have hget :
          getRightAt0 M (b :: bs).length t
              (boundedExecTableauCNF_NTM M (b :: bs) t) i =
            some (some (bs.getD i false)) := by
        rw [getRightAt0_boundedExecTableau M (b :: bs) t i hRadius]
        simp [inputTape, M.blank_none, map_some_getD_of_lt bs i hi]
      rw [readRightBits]
      rw [hget]
      have hspan' : (i + 1) + count ≤ bs.length := by omega
      rw [ih (i + 1) hspan']
      rfl

@[simp] theorem extractInitialTape_boundedExecTableau
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    extractInitialTape M x.length t
        (boundedExecTableauCNF_NTM M x t) =
      some x := by
  cases x with
  | nil =>
      simp [extractInitialTape, getHeadAt0_boundedExecTableau, inputTape]
  | cons b bs =>
      have htail :
          readRightBits M (b :: bs).length t
              (boundedExecTableauCNF_NTM M (b :: bs) t) 0 bs.length =
            some bs := by
        rw [readRightBits_boundedExec_aux M b bs t 0 bs.length]
        · simp
        · simp
      simp [extractInitialTape, getHeadAt0_boundedExecTableau,
        inputTape, htail]

/-- Decode a source directly from canonical circuit-encoding bits. -/
def decodeSourceBits
    (M : PolyNTMCandidate)
    (n t : Nat)
    (bits : BitString) : Option BitString :=
  match decodeCircuit bits with
  | none => none
  | some c => decodeSource M n t c

/-- The concrete complemented Cook--Levin reduction retains its source. -/
theorem decodeSource_reduce
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeSourceBits
        (complementToNTMCandidate M)
        x.length
        (M.timeBound x.length)
        ((complementSemanticReduction M hTotal).reduce x) =
      some x := by
  unfold decodeSourceBits
  rw [decodeCircuit_reduce M hTotal x]
  simp [decodeSource]


end SourceRecovery
end Real
end MCore
