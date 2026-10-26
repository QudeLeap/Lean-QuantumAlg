/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Correctness
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual nearest acceptance in the same fresh-feedback storage

The seven checker references are the original retained destinations, structurally
transported into the one feedback scope. Recovery, verification and first-success
selection use their actual interpreter record. All Store, service, history, path
and reference information is retained. The weight identities accept arbitrary
subnormalized input states and do not supply a sampling probability bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

namespace Checkers

/-- The same physical destinations, ordered as the actual nearest attempt arguments. -/
def keys {ctx : RuntimeCtx .quantum} (checkers : Checkers ctx) : List StorageKey :=
  [checkers.inverseSuccess.key, checkers.candidate.key, checkers.reconstruction.key,
    checkers.scalarResult.key, checkers.targetAccepted.key, checkers.accepted.key,
    checkers.selected.key]

private lemma retained_keys_permutation (ctx : RuntimeCtx .quantum) :
    (retained ctx).keys.Perm (persistentKeys ctx 256 260) := by
  apply List.perm_iff_count.mpr
  intro key
  simp only [keys, retained, persistentKeys, List.count_cons, List.count_nil]
  omega

/-- Actual one-time retention gives seven distinct checker destinations. -/
lemma retained_keys_nodup (ctx : RuntimeCtx .quantum) : (retained ctx).keys.Nodup :=
  (retained_keys_permutation ctx).nodup_iff.mpr (persistentKeys_distinct ctx 256 260)

/-- Structural transport preserves every original checker key in the same order. -/
lemma keys_transport {outer inner : RuntimeCtx .quantum} (checkers : Checkers outer)
    (lift : Transport outer inner) : (checkers.transport lift).keys = checkers.keys := by
  simp only [keys, transport, Transport.liftWrite_key]

/-- Feedback allocation does not merge the seven retained destinations. -/
lemma transport_retained_keys_nodup {outer inner : RuntimeCtx .quantum}
    (lift : Transport (persistentCtx outer 256 260) inner) :
    ((retained outer).transport lift).keys.Nodup := by
  rw [keys_transport]
  exact retained_keys_nodup outer

/-- All original caller reads remain disjoint from the actual transported seven cells. -/
lemma transport_retained_keys_free {outer inner : RuntimeCtx .quantum}
    (lift : Transport (persistentCtx outer 256 260) inner) {shape : CShape}
    (observed : CInputRef outer shape) :
    ∀ key ∈ ((retained outer).transport lift).keys,
      key ∉ (lift.liftInput
        ((Recovery.persistentTransport outer).liftInput observed)).storageKeys := by
  intro key member
  rw [keys_transport] at member
  have separate := persistentInput_separate 256 260 observed key
    ((retained_keys_permutation outer).mem_iff.mp member)
  rw [persistentInput_storageKeys] at separate
  simpa only [Transport.liftInput_storageKeys] using separate

end Checkers

private lemma firstFour_free {P : StorageKey → Prop} (a b c d e f g : StorageKey)
    (free : ∀ key ∈ [a, b, c, d, e, f, g], P key) :
    ∀ key ∈ [a, b, c, d], P key := by
  intro key member
  cases member with
  | head => exact free a (List.Mem.head _)
  | tail _ second =>
    cases second with
    | head => exact free b (List.Mem.tail _
      (List.Mem.head _))
    | tail _ third =>
      cases third with
      | head => exact free c (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))
      | tail _ fourth =>
        cases fourth with
        | head => exact free d (List.Mem.tail _
      (List.Mem.tail _
            (List.Mem.tail _
      (List.Mem.head _))))
        | tail _ impossible => cases impossible

private def selectedValue {Value : Type} (prior current : Bool)
    (old candidate : Value) : Value :=
  if prior then old else if current then candidate else old

private lemma selectedValue_of_iff {Value : Type} (prior current : Bool) (eligible : Prop)
    {priorDecision : Decidable (prior = true)} {eligibleDecision : Decidable eligible}
    (old candidate : Value) (same : current = true ↔ eligible) :
    (@ite Value (prior = true) priorDecision old
      (@ite Value eligible eligibleDecision candidate old)) =
        selectedValue prior current old candidate := by
  by_cases before : prior = true
  · simp only [selectedValue, if_pos before]
  · simp only [selectedValue, if_neg before]
    by_cases good : eligible
    · simp only [if_pos good, if_pos (same.mpr good)]
    · simp only [if_neg good, if_neg (mt same.mp good)]

private lemma head_ne_member {Key : Type} (head : Key) (rest : List Key)
    (distinct : (head :: rest).Nodup) (item : Key) (member : List.Mem item rest) :
    item ≠ head := by
  intro same
  exact (List.rel_of_pairwise_cons (R := fun left right : Key => left ≠ right)
    distinct member) same.symm

private lemma first_five_sublist {Key : Type} (a b c d e f g : Key) :
    List.Sublist [a, b, c, d, e] [a, b, c, d, e, f, g] :=
  List.Sublist.cons_cons a
    (List.Sublist.cons_cons b
    (List.Sublist.cons_cons c
    (List.Sublist.cons_cons d
    (List.Sublist.cons_cons e
      (List.Sublist.cons f (List.Sublist.cons g List.Sublist.slnil))))))

private lemma first_five_nodup {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : [a, b, c, d, e].Nodup :=
  (first_five_sublist a b c d e f g).nodup distinct

private lemma after_first_sublist {Key : Type} (a b c d e f g : Key) :
    List.Sublist [b, c, d, e, f, g] [a, b, c, d, e, f, g] :=
  List.Sublist.cons a
    (List.Sublist.cons_cons b
    (List.Sublist.cons_cons c
    (List.Sublist.cons_cons d
    (List.Sublist.cons_cons e
    (List.Sublist.cons_cons f
    (List.Sublist.cons_cons g (List.Sublist.slnil)))))))

private lemma after_first_nodup {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : [b, c, d, e, f, g].Nodup :=
  (after_first_sublist a b c d e f g).nodup distinct

private lemma after_second_sublist {Key : Type} (a b c d e f g : Key) :
    List.Sublist [c, d, e, f, g] [a, b, c, d, e, f, g] :=
  List.Sublist.cons a (List.Sublist.cons b
    (List.Sublist.cons_cons c
    (List.Sublist.cons_cons d
    (List.Sublist.cons_cons e
    (List.Sublist.cons_cons f
    (List.Sublist.cons_cons g (List.Sublist.slnil)))))))

private lemma after_second_nodup {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : [c, d, e, f, g].Nodup :=
  (after_second_sublist a b c d e f g).nodup distinct

private lemma sixth_ne_first {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : f ≠ a :=
  head_ne_member a [b, c, d, e, f, g] distinct f
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))

private lemma seventh_ne_first {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : g ≠ a :=
  head_ne_member a [b, c, d, e, f, g] distinct g
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _))))))

private lemma sixth_ne_second {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : f ≠ b :=
  head_ne_member b [c, d, e, f, g] (after_first_nodup a b c d e f g distinct) f
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _))))

private lemma seventh_ne_second {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : g ≠ b :=
  head_ne_member b [c, d, e, f, g] (after_first_nodup a b c d e f g distinct) g
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))

private lemma sixth_ne_third {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : f ≠ c :=
  head_ne_member c [d, e, f, g] (after_second_nodup a b c d e f g distinct) f
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))

private lemma seventh_ne_third {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : g ≠ c :=
  head_ne_member c [d, e, f, g] (after_second_nodup a b c d e f g distinct) g
    (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _))))

private def SevenKeyFacts {Key : Type} (a b c d e f g : Key) : Prop :=
  [a, b, c, d, e].Nodup ∧ (f ≠ a ∧ g ≠ a) ∧ (f ≠ b ∧ g ≠ b) ∧ (f ≠ c ∧ g ≠ c)

private lemma seven_key_facts {Key : Type} (a b c d e f g : Key)
    (distinct : [a, b, c, d, e, f, g].Nodup) : SevenKeyFacts a b c d e f g :=
  ⟨first_five_nodup a b c d e f g distinct,
    ⟨sixth_ne_first a b c d e f g distinct, seventh_ne_first a b c d e f g distinct⟩,
    ⟨sixth_ne_second a b c d e f g distinct, seventh_ne_second a b c d e f g distinct⟩,
    ⟨sixth_ne_third a b c d e f g distinct, seventh_ne_third a b c d e f g distinct⟩⟩

private def flagEffect (R : Register) (actual flag : Bool) : Effect R :=
  if actual = flag then Effect.one R else Effect.zero R

private lemma zero_flag_weight {R : Register} (density : DensityOperator R)
    (zeroMass : density.mass = 0) (actual flag : Bool) :
    (flagEffect R actual flag).weight density = 0 := by
  unfold flagEffect
  split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero, zeroMass]

private lemma density_readWeight_eq {R : Register} (density : DensityOperator R)
    (actual expected flag : Bool) (same : 0 < density.mass → actual = expected) :
    (flagEffect R actual flag).weight density =
      (flagEffect R expected flag).weight density := by
  by_cases positive : 0 < density.mass
  · rw [same positive]
  · have zeroMass := le_antisymm (le_of_not_gt positive) density.mass_nonneg
    exact (zero_flag_weight density zeroMass actual flag).trans
      (zero_flag_weight density zeroMass expected flag).symm

private structure CheckerTail (ctx : RuntimeCtx .quantum) (width scalarWidth : Nat) where
  curve : CurveSpec width
  modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth
  sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))
  base : CInputRef ctx (PointShape width)
  target : CInputRef ctx (PointShape width)
  inverseSuccess : CWriteRef ctx .bit
  candidate : CWriteRef ctx (.unsignedWord scalarWidth)
  reconstruction : CWriteRef ctx .bit
  scalarResult : CWriteRef ctx (PointShape width)
  targetAccepted : CWriteRef ctx .bit
  accepted : CWriteRef ctx .bit
  selected : CWriteRef ctx (.unsignedWord scalarWidth)

namespace CheckerTail

variable {ctx : RuntimeCtx .quantum} {width scalarWidth : Nat}
    {services : ClassicalOracleModel} (tail : CheckerTail ctx width scalarWidth)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx :=
  Nearest.attemptInto
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    tail.accepted tail.selected

private def after (before : Store ctx × services.HiddenState) : Store ctx :=
  Nearest.attemptStore
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) tail.curve tail.modulus tail.sample
    tail.base tail.target tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult
    tail.targetAccepted tail.accepted tail.selected before

private def keys : List StorageKey :=
  [tail.inverseSuccess.key, tail.candidate.key, tail.reconstruction.key, tail.scalarResult.key,
    tail.targetAccepted.key, tail.accepted.key, tail.selected.key]

private def raw (store : Store ctx) :=
  ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest.outputCellsInput tail.modulus
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput (store.read tail.sample))

private def rawCandidate (store : Store ctx) : CShape.Value (.unsignedWord scalarWidth) :=
  (tail.raw store).second.first

private def eligible (basePoint targetPoint : Pure.Point tail.curve) (store : Store ctx) : Prop :=
  Nearest.SampleAccepted tail.curve tail.modulus basePoint targetPoint (store.read tail.sample)

private def eligibleBit (basePoint targetPoint : Pure.Point tail.curve)
    (store : Store ctx) : Bool :=
  @decide (tail.eligible basePoint targetPoint store) (Classical.propDecidable _)

private lemma eligibleBit_true (basePoint targetPoint : Pure.Point tail.curve) (store : Store ctx) :
    tail.eligibleBit basePoint targetPoint store = true ↔
      tail.eligible basePoint targetPoint store := by
  simp only [eligibleBit, decide_eq_true_eq]

private def flagRead (store : Store ctx) : Bool :=
  (store.read (.storage tail.accepted.toCStorageRef)).toBool

private def selectedRead (store : Store ctx) : Nat :=
  (store.read (.storage tail.selected.toCStorageRef)).toNat

private def RecordStatement : Prop :=
  ∃ record : Store ctx × services.HiddenState →
      (Store ctx × services.HiddenState) × (tail.code (services := services)).Path,
    (∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      (tail.code (services := services)).execute environment Reference state =
        state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
    ∀ before, (record before).1.1 = tail.after environment before

private lemma actualRecord : tail.RecordStatement environment := by
  unfold RecordStatement
  have actual := Nearest.attemptInto_actualRecord
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment)
    tail.curve tail.modulus tail.sample tail.base tail.target tail.inverseSuccess tail.candidate
    tail.reconstruction tail.scalarResult tail.targetAccepted tail.accepted tail.selected
  exact actual

private def checked (before : Store ctx × services.HiddenState) : Store ctx :=
  Nearest.recoveryStore
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    before

private def selectionInputs : ClassicalRoutines.FirstAccepted.Inputs ctx scalarWidth :=
  ⟨.storage tail.targetAccepted.toCStorageRef, .storage tail.candidate.toCStorageRef⟩

private lemma after_eq (before : Store ctx × services.HiddenState) :
    tail.after environment before = ClassicalRoutines.FirstAccepted.selectionWrite
      tail.selectionInputs tail.accepted tail.selected (tail.checked environment before) := by
  have source := Nearest.attemptStore_eq
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    tail.accepted tail.selected before
  exact source

private lemma after_read_other (before : Store ctx × services.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (acceptedFree : tail.accepted.key ∉ observed.storageKeys)
    (selectedFree : tail.selected.key ∉ observed.storageKeys) :
    (tail.after environment before).read observed =
      (tail.checked environment before).read observed := by
  have selected := ClassicalRoutines.FirstAccepted.selectionWrite_read_other
    (ctx := ctx) (width := scalarWidth) tail.selectionInputs tail.accepted tail.selected
    (tail.checked environment before) observed acceptedFree selectedFree
  exact (congrArg (fun store : Store ctx => store.read observed)
    (tail.after_eq environment before)).trans selected

private lemma checked_inverse (before : Store ctx × services.HiddenState)
    (distinct : [tail.inverseSuccess.key, tail.candidate.key, tail.reconstruction.key,
      tail.scalarResult.key, tail.targetAccepted.key].Nodup) :
    (tail.checked environment before).read (.storage tail.inverseSuccess.toCStorageRef) =
      (tail.raw before.1).first := by
  rcases before with ⟨initialStore, initialHidden⟩
  have source := Nearest.recoveryStore_observations
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    initialStore initialHidden distinct
  exact source.1

private lemma checked_candidate (before : Store ctx × services.HiddenState)
    (distinct : [tail.inverseSuccess.key, tail.candidate.key, tail.reconstruction.key,
      tail.scalarResult.key, tail.targetAccepted.key].Nodup) :
    (tail.checked environment before).read (.storage tail.candidate.toCStorageRef) =
      (tail.raw before.1).second.first := by
  rcases before with ⟨initialStore, initialHidden⟩
  have source := Nearest.recoveryStore_observations
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    initialStore initialHidden distinct
  exact source.2.1

private lemma checked_reconstruction (before : Store ctx × services.HiddenState)
    (distinct : [tail.inverseSuccess.key, tail.candidate.key, tail.reconstruction.key,
      tail.scalarResult.key, tail.targetAccepted.key].Nodup) :
    (tail.checked environment before).read (.storage tail.reconstruction.toCStorageRef) =
      (tail.raw before.1).second.second := by
  rcases before with ⟨initialStore, initialHidden⟩
  have source := Nearest.recoveryStore_observations
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    initialStore initialHidden distinct
  exact source.2.2

private def InverseObservation : Prop :=
  ∀ before, tail.keys.Nodup →
    (tail.after environment before).read (.storage tail.inverseSuccess.toCStorageRef) =
      (tail.raw before.1).first

private lemma inverse_observation : tail.InverseObservation environment := by
  intro before distinct
  have facts := seven_key_facts tail.inverseSuccess.key tail.candidate.key
    tail.reconstruction.key tail.scalarResult.key tail.targetAccepted.key tail.accepted.key
    tail.selected.key distinct
  exact (tail.after_read_other environment before (.storage tail.inverseSuccess.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.1.1)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.1.2)).trans
      (tail.checked_inverse environment before facts.1)

private def CandidateObservation : Prop :=
  ∀ before, tail.keys.Nodup →
    (tail.after environment before).read (.storage tail.candidate.toCStorageRef) =
      (tail.raw before.1).second.first

private lemma candidate_observation : tail.CandidateObservation environment := by
  intro before distinct
  have facts := seven_key_facts tail.inverseSuccess.key tail.candidate.key
    tail.reconstruction.key tail.scalarResult.key tail.targetAccepted.key tail.accepted.key
    tail.selected.key distinct
  exact (tail.after_read_other environment before (.storage tail.candidate.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.2.1.1)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.2.1.2)).trans
      (tail.checked_candidate environment before facts.1)

private def ReconstructionObservation : Prop :=
  ∀ before, tail.keys.Nodup →
    (tail.after environment before).read (.storage tail.reconstruction.toCStorageRef) =
      (tail.raw before.1).second.second

private lemma reconstruction_observation : tail.ReconstructionObservation environment := by
  intro before distinct
  have facts := seven_key_facts tail.inverseSuccess.key tail.candidate.key
    tail.reconstruction.key tail.scalarResult.key tail.targetAccepted.key tail.accepted.key
    tail.selected.key distinct
  exact (tail.after_read_other environment before (.storage tail.reconstruction.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.2.2.1)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using facts.2.2.2.2)).trans
      (tail.checked_reconstruction environment before facts.1)

private def Observations : Prop :=
  tail.InverseObservation environment ∧ tail.CandidateObservation environment ∧
    tail.ReconstructionObservation environment

private lemma observations : tail.Observations environment :=
  ⟨tail.inverse_observation environment, tail.candidate_observation environment,
    tail.reconstruction_observation environment⟩

private def Latches : Prop :=
  ∀ (before : Store ctx × services.HiddenState) (basePoint targetPoint : Pure.Point tail.curve),
    PointRepresents tail.curve (before.1.read tail.base) basePoint →
    PointRepresents tail.curve (before.1.read tail.target) targetPoint →
    tail.keys.Nodup → (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    let eligible := tail.eligible basePoint targetPoint before.1
    let after := tail.after environment before
    (tail.flagRead after = true ↔ tail.flagRead before.1 = true ∨ eligible) ∧
      after.read (.storage tail.selected.toCStorageRef) =
        selectedValue (tail.flagRead before.1) (tail.eligibleBit basePoint targetPoint before.1)
          (before.1.read (.storage tail.selected.toCStorageRef)) (tail.rawCandidate before.1)

private lemma latches : tail.Latches environment := by
  intro before basePoint targetPoint baseRep targetRep distinct baseFree targetFree
  rcases before with ⟨initialStore, initialHidden⟩
  have source := Nearest.attemptStore_latches
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
    (environment := environment) tail.curve tail.modulus tail.sample tail.base tail.target
    tail.inverseSuccess tail.candidate tail.reconstruction tail.scalarResult tail.targetAccepted
    tail.accepted tail.selected initialStore initialHidden basePoint targetPoint baseRep targetRep
    distinct (firstFour_free _ _ _ _ _ _ _ baseFree)
    (firstFour_free _ _ _ _ _ _ _ targetFree)
  dsimp only at source ⊢
  constructor
  · exact source.1
  · refine source.2.trans ?_
    apply selectedValue_of_iff
    exact tail.eligibleBit_true basePoint targetPoint initialStore

private def Soundness : Prop :=
  ∀ (before : Store ctx × services.HiddenState) (basePoint targetPoint : Pure.Point tail.curve),
    PointRepresents tail.curve (before.1.read tail.base) basePoint →
    PointRepresents tail.curve (before.1.read tail.target) targetPoint →
    tail.keys.Nodup → (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    (tail.flagRead before.1 = true → tail.selectedRead before.1 • basePoint = targetPoint) →
    tail.flagRead (tail.after environment before) = true →
    tail.selectedRead (tail.after environment before) • basePoint = targetPoint

private lemma soundness : tail.Soundness environment := by
  intro before basePoint targetPoint baseRep targetRep distinct baseFree targetFree prior current
  exact Nearest.attemptStore_preserves_soundness
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment)
    tail.curve tail.modulus tail.sample tail.base tail.target tail.inverseSuccess tail.candidate
    tail.reconstruction tail.scalarResult tail.targetAccepted tail.accepted tail.selected
    before.1 before.2 basePoint targetPoint baseRep targetRep distinct
    (firstFour_free _ _ _ _ _ _ _ baseFree)
    (firstFour_free _ _ _ _ _ _ _ targetFree)
    prior current

private def readWeight {Reference : Register} {Label : Type} [Fintype Label]
    (state : State ctx Reference Label) (read : Store ctx → Bool) (flag : Bool) : ℝ :=
  state.effectWeight (fun entry => flagEffect (ctx.register.prod Reference)
    (read entry.1) flag)

private lemma record_readWeight
    (program : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × services.HiddenState →
      (Store ctx × services.HiddenState) × program.Path)
    (equation : program.execute environment Reference state = state.mapClassical
      (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (read : Store ctx → Bool) (flag : Bool) :
    readWeight (program.execute environment Reference state) read flag =
      state.effectWeight (fun entry => flagEffect (ctx.register.prod Reference)
        (read (record (entry.1, entry.2.1)).1.1) flag) := by
  unfold readWeight
  rw [equation, ExecutionState.effectWeight_mapClassical_decision]

private def FlagEquation : Prop :=
  ∀ (before : Store ctx × services.HiddenState) (basePoint targetPoint : Pure.Point tail.curve),
    PointRepresents tail.curve (before.1.read tail.base) basePoint →
    PointRepresents tail.curve (before.1.read tail.target) targetPoint →
    tail.keys.Nodup → (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    tail.flagRead (tail.after environment before) =
      (tail.flagRead before.1 || tail.eligibleBit basePoint targetPoint before.1)

private lemma flag_equation : tail.FlagEquation environment := by
  intro before basePoint targetPoint baseRep targetRep distinct baseFree targetFree
  have latch := tail.latches environment before basePoint targetPoint
    baseRep targetRep distinct baseFree targetFree
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.or_eq_true, eligibleBit_true] using latch.1

private def DensityFlagStatement : Prop :=
  ∀ {R : Register} (before : Store ctx × services.HiddenState)
    (basePoint targetPoint : Pure.Point tail.curve), tail.keys.Nodup →
    (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    ∀ (density : DensityOperator R),
    (0 < density.mass →
      PointRepresents tail.curve (before.1.read tail.base) basePoint ∧
      PointRepresents tail.curve (before.1.read tail.target) targetPoint) → ∀ flag : Bool,
    (flagEffect R (tail.flagRead (tail.after environment before)) flag).weight density =
      (flagEffect R (tail.flagRead before.1 ||
        tail.eligibleBit basePoint targetPoint before.1) flag).weight density

private lemma density_flag_weight : tail.DensityFlagStatement environment := by
  intro R before basePoint targetPoint distinct baseFree targetFree density represents flag
  exact density_readWeight_eq density (tail.flagRead (tail.after environment before))
    (tail.flagRead before.1 || tail.eligibleBit basePoint targetPoint before.1) flag
    (fun positive => tail.flag_equation environment before basePoint targetPoint
      (represents positive).1 (represents positive).2 distinct baseFree targetFree)

private def FlagWeight : Prop :=
  ∀ (basePoint targetPoint : Pure.Point tail.curve), tail.keys.Nodup →
    (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    (∀ entry, 0 < (state.block entry).mass →
      PointRepresents tail.curve (entry.1.read tail.base) basePoint ∧
      PointRepresents tail.curve (entry.1.read tail.target) targetPoint) → ∀ flag : Bool,
    readWeight ((tail.code (services := services)).execute environment Reference state)
        tail.flagRead flag =
      readWeight state (fun store => tail.flagRead store ||
        tail.eligibleBit basePoint targetPoint store) flag

private lemma flag_weight : tail.FlagWeight environment := by
  intro basePoint targetPoint distinct baseFree targetFree Reference History _ state represents flag
  obtain ⟨record, execution, stores⟩ := tail.actualRecord environment
  have weighted := record_readWeight (environment := environment)
    (tail.code (services := services)) state record (execution Reference state) tail.flagRead flag
  rw [weighted]
  unfold readWeight ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro entry _
  dsimp only
  rw [stores]
  exact tail.density_flag_weight environment (entry.1, entry.2.1) basePoint targetPoint
    distinct baseFree targetFree (state.block entry) (represents entry) flag

end CheckerTail

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def checkerTail : CheckerTail ctx 256 260 where
  curve := original.curve
  modulus := original.order
  sample := Recovery.pairedInput sampler
  base := original.base
  target := original.target
  inverseSuccess := checkers.inverseSuccess
  candidate := checkers.candidate
  reconstruction := checkers.reconstruction
  scalarResult := checkers.scalarResult
  targetAccepted := checkers.targetAccepted
  accepted := checkers.accepted
  selected := checkers.selected

/-- The exact full actual record of the original explicit-seven checker tail. -/
lemma checker_actualRecord : (original.checkerTail sampler checkers).RecordStatement environment :=
  CheckerTail.actualRecord _ environment

/-- The actual returned Store of that same nearest-recovery invocation. -/
def checkerStore (before : Store ctx × services.HiddenState) : Store ctx :=
  (original.checkerTail sampler checkers).after environment before

/-- Exact paid inverse, candidate and reconstruction observations survive the selection tail. -/
lemma checkerStore_observations :
    (original.checkerTail sampler checkers).Observations environment :=
  CheckerTail.observations _ environment

/-- Paid recovery and verification update the same original first-success latch. -/
lemma checkerStore_latches : (original.checkerTail sampler checkers).Latches environment :=
  CheckerTail.latches _ environment

/-- A sound prior original latch stays sound after this explicit-seven invocation. -/
lemma checkerStore_preserves_soundness :
    (original.checkerTail sampler checkers).Soundness environment :=
  CheckerTail.soundness _ environment

/-- Every structural caller observation outside those seven destinations remains unchanged. -/
lemma checkerStore_preserves_read (before : Store ctx × services.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ checkers.keys, key ∉ observed.storageKeys) :
    (original.checkerStore sampler checkers environment before).read observed =
      before.1.read observed :=
  Nearest.attemptStore_preserves_read
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) original.curve original.order
    (Recovery.pairedInput sampler) original.base original.target checkers.inverseSuccess
    checkers.candidate checkers.reconstruction checkers.scalarResult checkers.targetAccepted
    checkers.accepted checkers.selected before.1 before.2 observed free

/-- Exact checked single-attempt flag weights, for arbitrary subnormalized input and Reference. -/
lemma checker_flag_weight : (original.checkerTail sampler checkers).FlagWeight environment :=
  CheckerTail.flag_weight _ environment

end Inputs

namespace Inputs

variable {outer inner : RuntimeCtx .quantum} (original : Inputs outer)
    (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)

/-- The factory derives all separation for its original checker cells under feedback allocation. -/
lemma transported_checker_separation :
    let current := (original.transport (Recovery.persistentTransport outer)
      (Recovery.persistent_wires outer)).transport lift same
    let checkers := (Checkers.retained outer).transport lift
    checkers.keys.Nodup ∧
      (∀ key ∈ checkers.keys, key ∉ current.base.storageKeys) ∧
      (∀ key ∈ checkers.keys, key ∉ current.target.storageKeys) := by
  dsimp only
  refine ⟨Checkers.transport_retained_keys_nodup lift, ?_, ?_⟩
  · exact Checkers.transport_retained_keys_free lift original.base
  · exact Checkers.transport_retained_keys_free lift original.target

/-- Borrowed original base, target and every other structural read survive the actual tail. -/
lemma transported_checker_preserves_read {services : ClassicalOracleModel}
    (sampler : Sampling.Parameters inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store inner × services.HiddenState)
    {shape : CShape} (observed : CInputRef outer shape) :
    let current := (original.transport (Recovery.persistentTransport outer)
      (Recovery.persistent_wires outer)).transport lift same
    let checkers := (Checkers.retained outer).transport lift
    let read := lift.liftInput ((Recovery.persistentTransport outer).liftInput observed)
    (current.checkerStore sampler checkers environment before).read read = before.1.read read := by
  dsimp only
  exact checkerStore_preserves_read _ sampler _ environment before _
    (Checkers.transport_retained_keys_free lift observed)

private def TransportedFlagStatement : Prop :=
  ∀ {services : ClassicalOracleModel} (sampler : Sampling.Parameters inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment),
    let current := (original.transport (Recovery.persistentTransport outer)
      (Recovery.persistent_wires outer)).transport lift same
    let checkers := (Checkers.retained outer).transport lift
    let tail := current.checkerTail sampler checkers
    ∀ (basePoint targetPoint : Pure.Point tail.curve)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State inner Reference (services.HiddenState × History)),
      (∀ entry, 0 < (state.block entry).mass →
        PointRepresents tail.curve (entry.1.read tail.base) basePoint ∧
        PointRepresents tail.curve (entry.1.read tail.target) targetPoint) → ∀ flag : Bool,
      CheckerTail.readWeight
        ((tail.code (services := services)).execute environment Reference state)
          tail.flagRead flag =
        CheckerTail.readWeight state
          (fun store => tail.flagRead store || tail.eligibleBit basePoint targetPoint store) flag

/-- Actual original retained cells satisfy single-attempt acceptance without caller separation. -/
lemma transported_checker_flag_weight : original.TransportedFlagStatement lift same := by
  intro services sampler environment
  dsimp only
  have separated := original.transported_checker_separation lift same
  intro basePoint targetPoint Reference History _ state represents flag
  exact checker_flag_weight _ sampler _ environment basePoint targetPoint
    separated.1 separated.2.1 separated.2.2 state represents flag

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
