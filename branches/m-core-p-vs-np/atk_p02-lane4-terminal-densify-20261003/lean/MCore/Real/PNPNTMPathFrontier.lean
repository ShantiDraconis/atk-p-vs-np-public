
import MCore.Real.PNPNTMTableauFrontier

namespace MCore
namespace Real
namespace PNPNTMPathFrontier

open CanonicalFinalProof

abbrev NTMConfig (M : PolyNTMCandidate) :=
  Configuration (Fin (M.stateCount + 1)) (Option Bool)

def NTMHalted
    (M : PolyNTMCandidate)
    (c : NTMConfig M) : Prop :=
  M.machine.accepting c.state = true \/
    M.machine.rejecting c.state = true

def NTMActive
    (M : PolyNTMCandidate)
    (c : NTMConfig M) : Prop :=
  ¬ NTMHalted M c

/--
One exact runBranches step:
- halted configurations persist unchanged;
- active configurations take one listed nondeterministic successor.
-/
def NTMTableauStep
    (M : PolyNTMCandidate)
    (c c' : NTMConfig M) : Prop :=
  (NTMHalted M c ∧ c' = c) \/
  (NTMActive M c ∧ c' ∈ M.machine.successors c)

/--
Exact-length sequential path matching the runBranches fuel convention.
At fuel t there are t+1 snapshots.
-/
def NTMTableauPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M)
    (path : Fin (t + 1) -> NTMConfig M) : Prop :=
  path 0 = c0 ∧
    ∀ i : Fin t,
      NTMTableauStep M (path i.castSucc) (path i.succ)

/--
The endpoint of an exact-length path is accepting.
-/
def NTMTableauAcceptingPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M) : Prop :=
  ∃ path : Fin (t + 1) -> NTMConfig M,
    NTMTableauPath M t c0 path ∧
    M.machine.accepting (path (Fin.last t)).state = true

/--
Generic append-distribution lemma for runBranches.
The old repository had a machine-specific version for witnessGuessMachine;
this is the machine-independent form needed by the NTM tableau proof.
-/
theorem mem_runBranches_append
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs ys : List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel (xs ++ ys) <->
      z ∈ M.runBranches fuel xs \/
      z ∈ M.runBranches fuel ys := by
  induction fuel generalizing xs ys with
  | zero =>
      simp [NTM.runBranches]
  | succ fuel ih =>
      simp only [NTM.runBranches, List.filter_append, List.flatMap_append]
      rw [ih]
      simp only [ih]
      simpa [or_assoc, or_left_comm, or_comm]



theorem runBranches_nil
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat) :
    M.runBranches fuel [] = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simpa [NTM.runBranches] using ih

theorem runBranches_halted_singleton
    (M : PolyNTMCandidate)
    (c : NTMConfig M)
    (fuel : Nat)
    (h : NTMHalted M c) :
    M.machine.runBranches fuel [c] = [c] := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [NTM.runBranches]
      have hHalted :
          [c].filter (fun q =>
            M.machine.accepting q.state || M.machine.rejecting q.state) = [c] := by
        rcases h with ha | hr
        · simp [ha]
        · simp [hr]
      have hActive :
          [c].filter (fun q =>
            !(M.machine.accepting q.state || M.machine.rejecting q.state)) = [] := by
        rcases h with ha | hr
        · simp [ha]
        · simp [hr]
      rw [hHalted, hActive]
      simpa using ih

theorem mem_runBranches_flatMap
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs : List (Configuration State Symbol))
    (f : Configuration State Symbol -> List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel (xs.flatMap f) <->
      ∃ x ∈ xs, z ∈ M.runBranches fuel (f x) := by
  induction xs with
  | nil =>
      simp [runBranches_nil]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [mem_runBranches_append M fuel (f x) (xs.flatMap f) z]
      rw [ih]
      constructor
      · intro h
        rcases h with hx | hrest
        · exact ⟨x, by simp, hx⟩
        · rcases hrest with ⟨y, hy, hz⟩
          exact ⟨y, by simp [hy], hz⟩
      · rintro ⟨y, hy, hz⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl hz
        · exact Or.inr ⟨y, hy, hz⟩



/--
Recursive exact-fuel path relation matching runBranches.
This is an induction-friendly form used to prove the Fin-indexed tableau path
equivalence without reopening runBranches in later proofs.
-/
inductive NTMRunPath (M : PolyNTMCandidate) :
    Nat -> NTMConfig M -> NTMConfig M -> Prop where
  | zero (c : NTMConfig M) :
      NTMRunPath M 0 c c
  | halted
      {fuel : Nat} {c z : NTMConfig M}
      (hhalt : NTMHalted M c)
      (tail : NTMRunPath M fuel c z) :
      NTMRunPath M (fuel + 1) c z
  | active
      {fuel : Nat} {c c1 z : NTMConfig M}
      (hactive : NTMActive M c)
      (hstep : c1 ∈ M.machine.successors c)
      (tail : NTMRunPath M fuel c1 z) :
      NTMRunPath M (fuel + 1) c z

theorem runBranches_singleton_succ_halted
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c : NTMConfig M)
    (h : NTMHalted M c) :
    M.machine.runBranches (fuel + 1) [c] =
      M.machine.runBranches fuel [c] := by
  rw [NTM.runBranches]
  have hHalted :
      [c].filter (fun q =>
        M.machine.accepting q.state || M.machine.rejecting q.state) = [c] := by
    rcases h with ha | hr
    · simp [ha]
    · simp [hr]
  have hActive :
      [c].filter (fun q =>
        !(M.machine.accepting q.state || M.machine.rejecting q.state)) = [] := by
    rcases h with ha | hr
    · simp [ha]
    · simp [hr]
  rw [hHalted, hActive]
  rfl

theorem runBranches_singleton_succ_active
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c : NTMConfig M)
    (h : NTMActive M c) :
    M.machine.runBranches (fuel + 1) [c] =
      M.machine.runBranches fuel (M.machine.successors c) := by
  have hacc : M.machine.accepting c.state = false := by
    cases ha : M.machine.accepting c.state with
    | false => rfl
    | true =>
        exfalso
        apply h
        exact Or.inl ha
  have hrej : M.machine.rejecting c.state = false := by
    cases hr : M.machine.rejecting c.state with
    | false => rfl
    | true =>
        exfalso
        apply h
        exact Or.inr hr
  rw [NTM.runBranches]
  have hHalted :
      [c].filter (fun q =>
        M.machine.accepting q.state || M.machine.rejecting q.state) = [] := by
    simp [hacc, hrej]
  have hActive :
      [c].filter (fun q =>
        !(M.machine.accepting q.state || M.machine.rejecting q.state)) = [c] := by
    simp [hacc, hrej]
  rw [hHalted, hActive]
  simp

def RunBranchesPathEquivalence : Prop :=
  ∀ (M : PolyNTMCandidate) (fuel : Nat) (c z : NTMConfig M),
    z ∈ M.machine.runBranches fuel [c] <->
      NTMRunPath M fuel c z


theorem mem_runBranches_list_iff_exists_singleton
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs : List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel xs <->
      ∃ x ∈ xs, z ∈ M.runBranches fuel [x] := by
  have hflat :
      xs.flatMap (fun x => [x]) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [ih]
  have h :=
    mem_runBranches_flatMap M fuel xs (fun x => [x]) z
  simpa [hflat] using h

theorem runBranches_iff_runPath
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c z : NTMConfig M) :
    z ∈ M.machine.runBranches fuel [c] <->
      NTMRunPath M fuel c z := by
  induction fuel generalizing c z with
  | zero =>
      constructor
      · intro h
        simp [NTM.runBranches] at h
        subst z
        exact NTMRunPath.zero c
      · intro h
        cases h with
        | zero =>
            simp [NTM.runBranches]
  | succ fuel ih =>
      by_cases hh : NTMHalted M c
      · rw [runBranches_singleton_succ_halted M fuel c hh]
        constructor
        · intro hz
          exact NTMRunPath.halted hh ((ih c z).mp hz)
        · intro hp
          cases hp with
          | halted _ tail =>
              exact (ih c z).mpr tail
          | active hactive _ _ =>
              exact False.elim (hactive hh)
      · have ha : NTMActive M c := hh
        rw [runBranches_singleton_succ_active M fuel c ha]
        rw [mem_runBranches_list_iff_exists_singleton
              M.machine fuel (M.machine.successors c) z]
        constructor
        · rintro ⟨c1, hc1, hz⟩
          exact NTMRunPath.active ha hc1 ((ih c1 z).mp hz)
        · intro hp
          cases hp with
          | halted hhalt _ =>
              exact False.elim (ha hhalt)
          | active _ hc1 tail =>
              exact ⟨_, hc1, (ih _ _).mpr tail⟩

theorem runBranchesPathEquivalence_closed :
    RunBranchesPathEquivalence := by
  intro M fuel c z
  exact runBranches_iff_runPath M fuel c z

/--
Exact target lemma for the tableau.  It is deliberately stated separately:
the next proof step is the induction relating singleton runBranches membership
to NTMTableauStep paths.
-/
def AcceptsWithinPathEquivalence : Prop :=
  ∀ (M : PolyNTMCandidate) (t : Nat) (c0 : NTMConfig M),
    M.machine.AcceptsWithin t c0 <->
      NTMTableauAcceptingPath M t c0



/--
Prepend one configuration to a Fin-indexed path.
Index 0 is the new head; successor indices are read from the tail path.
-/
def prependFinPath
    {n : Nat} {α : Type}
    (head : α)
    (tail : Fin (n + 1) -> α) :
    Fin (n + 2) -> α :=
  Fin.cases head tail

@[simp] theorem prependFinPath_zero
    {n : Nat} {α : Type}
    (head : α) (tail : Fin (n + 1) -> α) :
    prependFinPath head tail 0 = head := by
  rfl

@[simp] theorem prependFinPath_succ
    {n : Nat} {α : Type}
    (head : α) (tail : Fin (n + 1) -> α)
    (i : Fin (n + 1)) :
    prependFinPath head tail i.succ = tail i := by
  rfl

@[simp] theorem prependFinPath_last
    {n : Nat} {α : Type}
    (head : α) (tail : Fin (n + 1) -> α) :
    prependFinPath head tail (Fin.last (n + 1)) =
      tail (Fin.last n) := by
  rfl

theorem runPath_to_finPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c z : NTMConfig M)
    (h : NTMRunPath M t c z) :
    ∃ path : Fin (t + 1) -> NTMConfig M,
      NTMTableauPath M t c path ∧
      path (Fin.last t) = z := by
  induction h with
  | zero c =>
      refine ⟨fun _ => c, ?_, rfl⟩
      constructor
      · rfl
      · intro i
        exact Fin.elim0 i
  | @halted fuel c z hhalt tail ih =>
      rcases ih with ⟨path, hpath, hlast⟩
      let path' : Fin (fuel + 2) -> NTMConfig M :=
        prependFinPath c path
      refine ⟨path', ?_, ?_⟩
      · constructor
        · simp [path', prependFinPath]
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · left
            refine ⟨hhalt, ?_⟩
            change path 0 = c
            exact hpath.1
          · simpa [path', prependFinPath] using hpath.2 j
      · simpa [path', prependFinPath] using hlast
  | @active fuel c c1 z hactive hstep tail ih =>
      rcases ih with ⟨path, hpath, hlast⟩
      let path' : Fin (fuel + 2) -> NTMConfig M :=
        prependFinPath c path
      refine ⟨path', ?_, ?_⟩
      · constructor
        · simp [path', prependFinPath]
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · right
            refine ⟨hactive, ?_⟩
            change path 0 ∈ M.machine.successors c
            rw [hpath.1]
            exact hstep
          · simpa [path', prependFinPath] using hpath.2 j
      · simpa [path', prependFinPath] using hlast

/--
Tail of a nonempty Fin-indexed tableau path.
-/
def tailFinPath
    {n : Nat} {α : Type}
    (path : Fin (n + 2) -> α) :
    Fin (n + 1) -> α :=
  fun i => path i.succ

@[simp] theorem tailFinPath_last
    {n : Nat} {α : Type}
    (path : Fin (n + 2) -> α) :
    tailFinPath path (Fin.last n) =
      path (Fin.last (n + 1)) := by
  rfl

theorem tailFinPath_isPath
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c : NTMConfig M)
    (path : Fin (fuel + 2) -> NTMConfig M)
    (h : NTMTableauPath M (fuel + 1) c path) :
    NTMTableauPath M fuel (path 1) (tailFinPath path) := by
  constructor
  · rfl
  · intro i
    simpa [tailFinPath] using h.2 i.succ

theorem finPath_to_runPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c : NTMConfig M)
    (path : Fin (t + 1) -> NTMConfig M)
    (h : NTMTableauPath M t c path) :
    NTMRunPath M t c (path (Fin.last t)) := by
  induction t generalizing c with
  | zero =>
      have h0 : path 0 = c := h.1
      simpa [h0] using NTMRunPath.zero c
  | succ fuel ih =>
      let c1 : NTMConfig M := path 1
      let tail : Fin (fuel + 1) -> NTMConfig M :=
        tailFinPath path
      have htail :
          NTMTableauPath M fuel c1 tail := by
        simpa [c1, tail] using
          tailFinPath_isPath M fuel c path h
      have hrun :
          NTMRunPath M fuel c1 (tail (Fin.last fuel)) :=
        ih c1 tail htail
      have hfirst :
          NTMTableauStep M c c1 := by
        have hs := h.2 (0 : Fin (fuel + 1))
        simpa [c1, h.1] using hs
      rcases hfirst with hhalt | hactive
      · rcases hhalt with ⟨hcHalt, hc1⟩
        have hrun' :
            NTMRunPath M fuel c (tail (Fin.last fuel)) := by
          simpa [hc1] using hrun
        have hout :
            NTMRunPath M (fuel + 1) c
              (tail (Fin.last fuel)) :=
          NTMRunPath.halted hcHalt hrun'
        simpa [tail] using hout
      · rcases hactive with ⟨hcActive, hc1mem⟩
        have hout :
            NTMRunPath M (fuel + 1) c
              (tail (Fin.last fuel)) :=
          NTMRunPath.active hcActive hc1mem hrun
        simpa [tail] using hout

theorem acceptsWithin_to_path
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M)
    (h : M.machine.AcceptsWithin t c0) :
    NTMTableauAcceptingPath M t c0 := by
  rcases h with ⟨z, hzrun, hzacc⟩
  have hr : NTMRunPath M t c0 z :=
    (runBranches_iff_runPath M t c0 z).mp hzrun
  rcases runPath_to_finPath M t c0 z hr with
    ⟨path, hpath, hlast⟩
  refine ⟨path, hpath, ?_⟩
  simpa [hlast] using hzacc

theorem path_to_acceptsWithin
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M)
    (h : NTMTableauAcceptingPath M t c0) :
    M.machine.AcceptsWithin t c0 := by
  rcases h with ⟨path, hpath, hacc⟩
  refine ⟨path (Fin.last t), ?_, hacc⟩
  exact (runBranches_iff_runPath M t c0
    (path (Fin.last t))).mpr
      (finPath_to_runPath M t c0 path hpath)

theorem acceptsWithin_iff_path :
    AcceptsWithinPathEquivalence := by
  intro M t c0
  constructor
  · exact acceptsWithin_to_path M t c0
  · exact path_to_acceptsWithin M t c0

def PNP_NTM_PATH_OPEN_MATH : Prop :=
  AcceptsWithinPathEquivalence

#print axioms MCore.Real.PNPNTMPathFrontier.mem_runBranches_append

end PNPNTMPathFrontier
end Real
end MCore
