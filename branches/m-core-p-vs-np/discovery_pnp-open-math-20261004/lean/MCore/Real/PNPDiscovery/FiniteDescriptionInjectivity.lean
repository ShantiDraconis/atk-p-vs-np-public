import MCore.Real.PNPDiscovery.FiniteCandidateGodelWords

namespace MCore
namespace Real
namespace PNPDiscovery

/-- Header projection of the finite word payload. -/
def finiteDescriptionHeader
    (D : FiniteCandidateDescription) : List Nat :=
  [D.stateCount,
   D.initial.val,
   D.clockCoefficient,
   D.clockExponent]

@[simp] theorem finiteDescriptionWords_take4
    (D : FiniteCandidateDescription) :
    (finiteDescriptionWords D).take 4 =
      finiteDescriptionHeader D := by
  simp [finiteDescriptionWords, finiteDescriptionHeader]

theorem words_eq_stateCount
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    A.stateCount = B.stateCount := by
  have ht := congrArg (fun xs : List Nat => xs.take 4) h
  simp [finiteDescriptionWords_take4,
    finiteDescriptionHeader] at ht
  exact ht.1

theorem words_eq_clockCoefficient
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    A.clockCoefficient = B.clockCoefficient := by
  have ht := congrArg (fun xs : List Nat => xs.take 4) h
  simp [finiteDescriptionWords_take4,
    finiteDescriptionHeader] at ht
  exact ht.2.2.1

theorem words_eq_clockExponent
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    A.clockExponent = B.clockExponent := by
  have ht := congrArg (fun xs : List Nat => xs.take 4) h
  simp [finiteDescriptionWords_take4,
    finiteDescriptionHeader] at ht
  exact ht.2.2.2

/-- Tail after the four-word header. -/
def finiteDescriptionBody
    (D : FiniteCandidateDescription) : List Nat :=
  transitionTableWords D ++
  haltingTableWords D ++
  acceptingTableWords D

@[simp] theorem finiteDescriptionWords_drop4
    (D : FiniteCandidateDescription) :
    (finiteDescriptionWords D).drop 4 =
      finiteDescriptionBody D := by
  simp [finiteDescriptionWords, finiteDescriptionBody]

/-- Transition region has a length determined solely by stateCount. -/
def transitionWordCount (q : Nat) : Nat :=
  (q + 1) * 9

def boolTableWordCount (q : Nat) : Nat :=
  q + 1

theorem body_take_transition
    (D : FiniteCandidateDescription) :
    (finiteDescriptionBody D).take
        (transitionWordCount D.stateCount) =
      transitionTableWords D := by
  unfold finiteDescriptionBody transitionWordCount
  rw [List.take_append_of_le]
  · rfl
  · rw [transitionTableWords_length]
    omega

theorem body_drop_transition_take_halting
    (D : FiniteCandidateDescription) :
    ((finiteDescriptionBody D).drop
        (transitionWordCount D.stateCount)).take
          (boolTableWordCount D.stateCount) =
      haltingTableWords D := by
  unfold finiteDescriptionBody transitionWordCount boolTableWordCount
  rw [List.drop_append_of_le]
  · simp [transitionTableWords_length,
      haltingTableWords_length]
  · rw [transitionTableWords_length]
    omega

theorem body_drop_transition_halting
    (D : FiniteCandidateDescription) :
    (finiteDescriptionBody D).drop
        (transitionWordCount D.stateCount +
          boolTableWordCount D.stateCount) =
      acceptingTableWords D := by
  unfold finiteDescriptionBody transitionWordCount boolTableWordCount
  rw [List.drop_append_of_le]
  · rw [transitionTableWords_length]
    simp
    rw [List.drop_append_of_le]
    · simp [haltingTableWords_length]
    · rw [haltingTableWords_length]
  · rw [transitionTableWords_length]
    omega

/-- Equality of complete words yields equality of flattened transition words
once stateCount is aligned. -/
theorem words_eq_transitionWords
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    HEq (transitionTableWords A)
      (transitionTableWords B) := by
  have hs := words_eq_stateCount A B h
  subst B.stateCount
  have hb := congrArg
    (fun xs : List Nat =>
      (xs.drop 4).take
        (transitionWordCount A.stateCount)) h
  simpa [finiteDescriptionWords_drop4,
    body_take_transition] using hb

/-- Equality of complete words yields equality of flattened halting words. -/
theorem words_eq_haltingWords
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    HEq (haltingTableWords A)
      (haltingTableWords B) := by
  have hs := words_eq_stateCount A B h
  subst B.stateCount
  have hb := congrArg
    (fun xs : List Nat =>
      ((xs.drop 4).drop
        (transitionWordCount A.stateCount)).take
          (boolTableWordCount A.stateCount)) h
  simpa [finiteDescriptionWords_drop4,
    body_drop_transition_take_halting] using hb

/-- Equality of complete words yields equality of flattened accepting words. -/
theorem words_eq_acceptingWords
    (A B : FiniteCandidateDescription)
    (h : finiteDescriptionWords A =
      finiteDescriptionWords B) :
    HEq (acceptingTableWords A)
      (acceptingTableWords B) := by
  have hs := words_eq_stateCount A B h
  subst B.stateCount
  have hb := congrArg
    (fun xs : List Nat =>
      (xs.drop 4).drop
        (transitionWordCount A.stateCount +
          boolTableWordCount A.stateCount)) h
  simpa [finiteDescriptionWords_drop4,
    body_drop_transition_halting] using hb

/-- Remaining exact uniqueness atom:
flattened tables must be reflected back to dependent Fin-indexed functions.
This is finite extensionality only; no complexity endpoint appears. -/
def DependentFiniteTableExtensionality : Prop :=
  ∀ A B : FiniteCandidateDescription,
    A.stateCount = B.stateCount →
    HEq (transitionTableWords A) (transitionTableWords B) →
    HEq (haltingTableWords A) (haltingTableWords B) →
    HEq (acceptingTableWords A) (acceptingTableWords B) →
    A.initial.val = B.initial.val →
    A.clockCoefficient = B.clockCoefficient →
    A.clockExponent = B.clockExponent →
    A = B

/-- Once finite dependent-table extensionality is discharged, the word
representation is injective. -/
theorem dependentExtensionality_implies_words_injective
    (H : DependentFiniteTableExtensionality) :
    Function.Injective finiteDescriptionWords := by
  intro A B h
  apply H A B
  · exact words_eq_stateCount A B h
  · exact words_eq_transitionWords A B h
  · exact words_eq_haltingWords A B h
  · exact words_eq_acceptingWords A B h
  · have ht := congrArg (fun xs : List Nat => xs.take 4) h
    simp [finiteDescriptionWords_take4,
      finiteDescriptionHeader] at ht
    exact ht.2.1
  · exact words_eq_clockCoefficient A B h
  · exact words_eq_clockExponent A B h

/-- An injective word representation gives a noncomputable but exact
reconstructor by choosing the unique preimage when one exists. -/
noncomputable def reconstructorOfInjective
    (hinj : Function.Injective finiteDescriptionWords) :
    FiniteTableReconstructor where
  reconstruct := fun words =>
    if h : ∃ D : FiniteCandidateDescription,
        finiteDescriptionWords D = words then
      some (Classical.choose h)
    else
      none
  exact := by
    intro D
    simp only [dif_pos]
    · let h :
          ∃ E : FiniteCandidateDescription,
            finiteDescriptionWords E =
              finiteDescriptionWords D :=
        ⟨D, rfl⟩
      have hs :
          Classical.choose h = D := by
        apply hinj
        exact Classical.choose_spec h
      simp [h, hs]
    · exact ⟨D, rfl⟩

theorem dependentExtensionality_closes_reconstructor
    (H : DependentFiniteTableExtensionality) :
    FiniteTableReconstructorGap := by
  exact ⟨reconstructorOfInjective
    (dependentExtensionality_implies_words_injective H)⟩

/-- The Gödel-coding frontier has now been reduced to a single finite
extensionality theorem. -/
def CurrentFiniteCodecOpenAtom : Prop :=
  DependentFiniteTableExtensionality

#print axioms MCore.Real.PNPDiscovery.words_eq_stateCount
#print axioms MCore.Real.PNPDiscovery.words_eq_transitionWords
#print axioms MCore.Real.PNPDiscovery.dependentExtensionality_implies_words_injective
#print axioms MCore.Real.PNPDiscovery.dependentExtensionality_closes_reconstructor

end PNPDiscovery
end Real
end MCore
