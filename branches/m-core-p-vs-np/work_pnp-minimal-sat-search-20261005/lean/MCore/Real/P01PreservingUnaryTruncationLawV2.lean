import MCore.Real.P01PreservingUnaryReaderResiduals

namespace MCore.Real.P01PreservingUnaryTruncationLawV2

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate

abbrev ConcreteClosureWitness := PreservingUnaryReaderCertificate

structure ReaderInput where
  witness : BitString
  index : Nat
  valid : index < witness.length

def ReaderInput.size (x : ReaderInput) : Nat :=
  x.witness.length + (encodeNat x.index).length

def ReaderInput.initialConfig (x : ReaderInput) :
    Configuration PreservingReadState (Option Bool) :=
  { state := preservingUnaryReadMachine.initial
    tape := witnessReadTape x.witness x.index }

def budget (x : ReaderInput) : Nat :=
  preservingUnaryTimeBound x.size

structure ExhaustionCertificate where
  halts :
    ∀ x : ReaderInput,
      preservingUnaryReadMachine.HaltsWithin (budget x) x.initialConfig

structure CorrectnessCertificate where
  correct :
    ∀ x : ReaderInput,
      preservingReadAccepting
        (preservingUnaryReadMachine.run (budget x) x.initialConfig).state =
      x.witness.getD x.index false

structure PreservationCertificate where
  preserves :
    ∀ x : ReaderInput,
      ∃ left right : List (Option Bool),
        (preservingUnaryReadMachine.run (budget x) x.initialConfig).tape =
          { left := left ++ x.witness.map some
            head := none
            right := right }

structure ConcreteSearchClosure where
  exhaustion : ExhaustionCertificate
  correctness : CorrectnessCertificate
  preservation : PreservationCertificate

def ConcreteSearchClosure.toReaderCertificate
    (C : ConcreteSearchClosure) : ConcreteClosureWitness := by
  let hhalts : PreservingUnaryHalts := by
    intro witness i hi
    exact C.exhaustion.halts ⟨witness, i, hi⟩
  let hcorrect : PreservingUnaryCorrect := by
    intro witness i hi
    exact C.correctness.correct ⟨witness, i, hi⟩
  let hpreserves : PreservingUnaryPreservesWitness := by
    intro witness i hi
    exact C.preservation.preserves ⟨witness, i, hi⟩
  exact residuals_close_preserving_unary_reader hhalts hcorrect hpreserves

structure LoopInvariant where
  input : ReaderInput
  stepA : Nat
  stepB : Nat

def LoopInvariant.Valid (I : LoopInvariant) : Prop :=
  I.stepA < I.stepB ∧
  I.stepB ≤ budget I.input ∧
  (preservingUnaryReadMachine.run I.stepA I.input.initialConfig).state =
    (preservingUnaryReadMachine.run I.stepB I.input.initialConfig).state

inductive SearchResult
  | found : ConcreteSearchClosure → SearchResult
  | exhausted : ExhaustionCertificate → SearchResult
  | loopDetected : (I : LoopInvariant) → I.Valid → SearchResult
  | open : SearchResult

structure TruncationLaw where
  exhaustionProducesClosure :
    ExhaustionCertificate → ConcreteSearchClosure
  loopProducesClosure :
    ∀ I : LoopInvariant, I.Valid → ConcreteSearchClosure

def SearchResult.close?
    (L : TruncationLaw) :
    SearchResult → Option ConcreteClosureWitness
  | .found C => some (ConcreteSearchClosure.toReaderCertificate C)
  | .exhausted E =>
      some (ConcreteSearchClosure.toReaderCertificate (L.exhaustionProducesClosure E))
  | .loopDetected I hI =>
      some (ConcreteSearchClosure.toReaderCertificate (L.loopProducesClosure I hI))
  | .open => none

theorem open_does_not_close (L : TruncationLaw) :
    SearchResult.close? L SearchResult.open = none := by
  rfl

theorem exhaustion_closes
    (L : TruncationLaw) (E : ExhaustionCertificate) :
    PreservingUnaryReaderGap :=
  ⟨ConcreteSearchClosure.toReaderCertificate (L.exhaustionProducesClosure E)⟩

theorem loop_closes
    (L : TruncationLaw) (I : LoopInvariant) (hI : I.Valid) :
    PreservingUnaryReaderGap := by
  let C : ConcreteSearchClosure := L.loopProducesClosure I hI
  exact ⟨ConcreteSearchClosure.toReaderCertificate C⟩

#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.ConcreteSearchClosure.toReaderCertificate
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.open_does_not_close
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.exhaustion_closes
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.loop_closes

end MCore.Real.P01PreservingUnaryTruncationLawV2
