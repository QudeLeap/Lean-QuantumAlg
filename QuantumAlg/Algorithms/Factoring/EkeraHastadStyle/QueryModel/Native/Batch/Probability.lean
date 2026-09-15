/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference
import all QuantumAlg.Util.PMF.VectorMass

/-!
# The actual fixed-bank sixteen-sample joint law

The loop consists of the existing sampler stages on one physical bank.
Its conditional product law follows from the proved observation equations
for every actual stage. The source is drawn by the existing uniform source
instruction, and all reference matrix coefficients remain explicit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem sampleRef_ne_liftSamples {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (width : Nat) (ref : CWriteRef ctx shape) (count : Nat)
    (index : Fin count) :
    (Slots.sampleRef ctx width count index).key ≠ (Slots.liftSamples width ref count).key := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ih previous) index
      intro same
      change (Slots.samples ctx width count).canonicalFreshKey =
        (Slots.liftSamples width ref count).key at same
      apply (Slots.samples ctx width count).canonicalFreshKey_fresh
      have present := MeasurementCells.reference_key_mem
        (Slots.liftSamples width ref count).toCStorageRef
      exact same.symm ▸ present

private def slotsInput {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (input : CInputRef ctx shape) :
    (count : Nat) → CInputRef (Slots.samples ctx width count) shape
  | 0 => input
  | count + 1 => (slotsInput width input count).underRetained
      (Slots.samples ctx width count).canonicalFreshKey (.bits width)
      (Slots.samples ctx width count).canonicalFreshKey_fresh

private theorem slotsInput_storage {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (ref : CWriteRef ctx shape) (count : Nat) :
    slotsInput width (.storage ref.toCStorageRef) count =
      .storage (Slots.liftSamples width ref count).toCStorageRef := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact congrArg
        (fun read : CInputRef (Slots.samples ctx width count) shape => read.underRetained
          (Slots.samples ctx width count).canonicalFreshKey (.bits width)
          (Slots.samples ctx width count).canonicalFreshKey_fresh) ih

private theorem slotsInput_product {ctx : RuntimeCtx .quantum} {left right : CShape}
    (width : Nat) (first : CInputRef ctx left) (second : CInputRef ctx right) (count : Nat) :
    slotsInput width (.product first second) count =
      .product (slotsInput width first count) (slotsInput width second count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact congrArg
        (fun read : CInputRef (Slots.samples ctx width count) (.product left right) =>
          read.underRetained (Slots.samples ctx width count).canonicalFreshKey (.bits width)
            (Slots.samples ctx width count).canonicalFreshKey_fresh) ih

private theorem slots_reference {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (input : CInputRef ctx shape) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Slots.allocateSamples ctx width count).execute Reference state)
      (fun entry _ => weight (entry.1.read (slotsInput width input count))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  induction count with
  | zero =>
      have executed := congrArg
        (fun output : State ctx Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
  | succ count ih =>
      let previous := Slots.allocateSamples ctx width count
      let retained := Circuit.retain (Slots.samples ctx width count)
        (Slots.samples ctx width count).canonicalFreshKey (.bits width)
        (Slots.samples ctx width count).canonicalFreshKey_fresh
      exact (Circuit.referenceFiberSum_execute_seq previous retained state
        (fun store => weight (store.read (slotsInput width input (count + 1))))
        leftRef rightRef).trans
        ((Circuit.referenceFiberSum_execute_retain_input (slotsInput width input count)
          (Slots.samples ctx width count).canonicalFreshKey (.bits width)
          (Slots.samples ctx width count).canonicalFreshKey_fresh
          (previous.execute Reference state) weight leftRef rightRef).trans ih)

private theorem liftedSamples_key {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (ref : CWriteRef ctx shape) (count : Nat) :
    (Slots.liftSamples width ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

attribute [local irreducible] Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem underBank_read {shape : CShape}
    (ref : CWriteRef (storageContext base N) shape) :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (.storage ref.toCStorageRef) = .storage (underBank base noQuantum N ref).toCStorageRef := by
  let bankRef : CWriteRef
      (bankContext (storageContext base N) (storage_empty base noQuantum N) N) shape :=
    { toCStorageRef := ref.toCStorageRef.underOwnedLayout
        (storageContext base N).canonicalFreshKey (layout N)
        (storageContext base N).canonicalFreshKey_fresh
        (allocationDisjoint (storageContext base N) (storage_empty base noQuantum N) N)
      writable := ref.writable }
  change (MeasurementCells.liftInput 2 (.storage bankRef.toCStorageRef)
    (measurementBits N)).underRetained
      (cellsContext (storageContext base N) (storage_empty base noQuantum N) N).canonicalFreshKey
      (.bits (measurementBits N)) _ = _
  rw [MeasurementCells.liftInput_storage 2 bankRef (measurementBits N)]
  rfl

private theorem lifted_measured_separate {shape : CShape}
    (observed : CInputRef (storageContext base N) shape) (index : Fin (measurementBits N)) :
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        observed).storageKeys := by
  let prior := MeasurementCells.liftInput 2
    (bankInput (storageContext base N) (storage_empty base noQuantum N) N observed)
    (measurementBits N)
  have keys := CInputRef.storageKeys_underRetained prior
    (cellsContext (storageContext base N) (storage_empty base noQuantum N) N).canonicalFreshKey
    (.bits (measurementBits N))
    (cellsContext (storageContext base N) (storage_empty base noQuantum N)
      N).canonicalFreshKey_fresh
  exact (congrArg (fun keys =>
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉ keys)
      keys).mpr (MeasurementCells.reference_not_mem_liftInput 2
        (bankInput (storageContext base N) (storage_empty base noQuantum N) N observed)
        (measurementBits N) index)

private theorem lifted_working_separate {shape : CShape}
    (observed : CInputRef (storageContext base N) shape) :
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        observed).storageKeys :=
  CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _

private theorem terminal_parameter_ne (index : Fin 16) :
    (terminalRef base noQuantum N index).key ≠ (parameterRef base noQuantum N).key := by
  intro same
  have leftKey := nativeOracle_underBank_key base noQuantum N
    (Slots.terminalRef (sourceContext base N) N index)
  have rightKey := nativeOracle_underBank_key base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))
  exact sampleRef_ne_liftSamples (measurementBits N)
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N) 16 index
    ((leftKey.symm.trans same).trans rightKey)

private theorem terminal_source_ne (index : Fin 16) :
    (terminalRef base noQuantum N index).key ≠ (sourceRef base noQuantum N).key := by
  intro same
  have leftKey := nativeOracle_underBank_key base noQuantum N
    (Slots.terminalRef (sourceContext base N) N index)
  have rightKey := nativeOracle_underBank_key base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact sampleRef_ne_liftSamples (measurementBits N)
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N) 16 index
    ((leftKey.symm.trans same).trans rightKey)

private theorem parameter_measured_separate (index : Fin (measurementBits N)) :
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (CInputRef.storage (parameterRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := nativeOracle_batch_parameter_read base noQuantum N
  exact (congrArg (fun read =>
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N (parameter base N) index)

private theorem parameter_working_separate :
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (parameterRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := nativeOracle_batch_parameter_read base noQuantum N
  exact (congrArg (fun read =>
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N (parameter base N))

private theorem terminal_measured_separate (written : Fin (measurementBits N)) (index : Fin 16) :
    (cells (storageContext base N) (storage_empty base noQuantum N) N written).key ∉
      (CInputRef.storage (terminalRef base noQuantum N index).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N (Slots.terminalRef (sourceContext base N) N index)
  exact (congrArg (fun read =>
    (cells (storageContext base N) (storage_empty base noQuantum N) N written).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N
      (CInputRef.storage (Slots.terminalRef (sourceContext base N) N index).toCStorageRef) written)

private theorem terminal_working_separate (index : Fin 16) :
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (terminalRef base noQuantum N index).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N (Slots.terminalRef (sourceContext base N) N index)
  exact (congrArg (fun read =>
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N
      (CInputRef.storage (Slots.terminalRef (sourceContext base N) N index).toCStorageRef))

private theorem source_measured_separate (index : Fin (measurementBits N)) :
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (CInputRef.storage (sourceRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact (congrArg (fun read =>
    (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N (CInputRef.storage (Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)).toCStorageRef) index)

private theorem source_working_separate :
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (sourceRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact (congrArg (fun read =>
    (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N (CInputRef.storage (Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)).toCStorageRef))

/-- The joint event reads the actual chronological terminal cells. -/
def terminalIndicator (count : Nat) (indices : Fin count → Fin 16)
    (outcomes : Fin count → Fin (measurementBits N) → Bool)
    (store : Store (context base noQuantum N)) : ℂ :=
  ∏ index : Fin count,
    if store.read (.storage (terminalRef base noQuantum N (indices index)).toCStorageRef) =
      CShape.Value.bits (outcomes index) then 1 else 0

private def conditionalProduct (count : Nat)
    (outcomes : Fin count → Fin (measurementBits N) → Bool)
    (parameter : (ParameterShape N).Value) : ℂ :=
  ∏ index : Fin count, ((selectedOutcomePMF parameter (outcomes index)).toReal : ℂ)

private theorem conditionalProduct_step (count : Nat)
    (outcomes : Fin (count + 1) → Fin (measurementBits N) → Bool)
    (parameter : (ParameterShape N).Value) (weight : ℂ) :
    (weight * conditionalProduct N count (fun index => outcomes index.succ) parameter) *
      ((selectedOutcomePMF parameter (outcomes 0)).toReal : ℂ) =
        weight * conditionalProduct N (count + 1) outcomes parameter := by
  unfold conditionalProduct
  rw [Fin.prod_univ_succ]
  ring

private theorem reference_congr {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (first second : Store (context base noQuantum N) → ℂ)
    (equal : ∀ store, first store = second store) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => first entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => second entry.1) leftRef rightRef :=
  congrArg (fun observe : Store (context base noQuantum N) → ℂ =>
    ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) leftRef rightRef)
      (funext equal)

private theorem range_reference (input : Input N) :
    ∀ (count : Nat) (indices : Fin count → Fin 16) (_distinct : Function.Injective indices)
      {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
      (_measuredSeparate : ∀ position,
        (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
          observed.storageKeys)
      (_workingSeparate :
        (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
          observed.storageKeys)
      (_slotSeparate : ∀ index,
        (terminalRef base noQuantum N (indices index)).key ∉ observed.storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State (context base noQuantum N) Reference History)
      (weight : (ParameterShape N).Value → shape.Value → ℂ)
      (outcomes : Fin count → Fin (measurementBits N) → Bool)
      (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum
        ((Circuit.forRange count (fun index =>
          reusedSample base noQuantum N input (indices index))).execute Reference state)
        (fun entry _ => weight
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (entry.1.read observed) *
          terminalIndicator base noQuantum N count indices outcomes entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read observed) * conditionalProduct N count outcomes
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef)))
        leftRef rightRef := by
  intro count
  induction count with
  | zero =>
      intro indices _distinct shape observed _measuredSeparate _workingSeparate
        _slotSeparate Reference History _ state weight outcomes leftRef rightRef
      have executed := Circuit.execute_id_mapClassical Reference state
      have mapped := congrArg
        (fun output : State (context base noQuantum N) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight
              (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
              (entry.1.read observed)) leftRef rightRef) executed
      have transported := mapped.trans (ExecutionState.referenceFiberSum_mapClassical
        state (fun entry => (entry.1, (entry.2, ()))) _ leftRef rightRef)
      simp only [terminalIndicator, conditionalProduct, Fin.prod_univ_zero, mul_one]
      convert transported using 1
      rfl
  | succ count ih =>
      intro indices distinct shape observed measuredSeparate workingSeparate
        slotSeparate Reference History _ state weight outcomes leftRef rightRef
      let head := terminalRef base noQuantum N (indices 0)
      let joint : CInputRef (context base noQuantum N)
          (.product shape (.bits (measurementBits N))) :=
        .product observed (.storage head.toCStorageRef)
      let first := reusedSample base noQuantum N input (indices 0)
      let rest := Circuit.forRange count fun index =>
        reusedSample base noQuantum N input (indices index.succ)
      let advanced := first.execute Reference state
      let headIndicator := fun value : (CShape.bits (measurementBits N)).Value =>
        if value = CShape.Value.bits (outcomes 0) then (1 : ℂ) else 0
      let tailWeight := fun parameter : (ParameterShape N).Value =>
        fun old : (CShape.product shape (.bits (measurementBits N))).Value =>
          weight parameter old.first * headIndicator old.second
      have tailDistinct : Function.Injective (fun index : Fin count => indices index.succ) :=
        fun _ _ same => Fin.succ_injective _ (distinct same)
      have tailMeasured : ∀ position,
          (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
            joint.storageKeys := by
        intro position present
        exact (List.mem_append.mp present).elim (measuredSeparate position)
          (terminal_measured_separate base noQuantum N position (indices 0))
      have tailWorking :
          (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
            joint.storageKeys := by
        intro present
        exact (List.mem_append.mp present).elim workingSeparate
          (terminal_working_separate base noQuantum N (indices 0))
      have tailSlots : ∀ index : Fin count,
          (terminalRef base noQuantum N (indices index.succ)).key ∉ joint.storageKeys := by
        intro index present
        rcases List.mem_append.mp present with original | headKey
        · exact slotSeparate index.succ original
        · have same := nativeOracle_batch_terminal_keys base noQuantum N
            (List.mem_singleton.mp headKey)
          have impossible := congrArg Fin.val (distinct same)
          simp only [Fin.val_succ, Fin.val_zero] at impossible
          omega
      have tailLaw := ih (fun index => indices index.succ) tailDistinct joint
        tailMeasured tailWorking tailSlots advanced tailWeight (fun index => outcomes index.succ)
        leftRef rightRef
      let finalWeight := fun store : Store (context base noQuantum N) =>
        weight (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (store.read observed) *
          terminalIndicator base noQuantum N (count + 1) indices outcomes store
      have aligned := reference_congr base noQuantum N (rest.execute Reference advanced)
        finalWeight (fun store => tailWeight
          (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (store.read joint) * terminalIndicator base noQuantum N count
            (fun index => indices index.succ) (fun index => outcomes index.succ) store)
        (fun store => by
          change weight _ _ * terminalIndicator base noQuantum N (count + 1)
            indices outcomes store =
            (weight _ _ * headIndicator (store.read (.storage head.toCStorageRef))) *
              terminalIndicator base noQuantum N count
                (fun index => indices index.succ) (fun index => outcomes index.succ) store
          rw [terminalIndicator, Fin.prod_univ_succ]
          exact (mul_assoc _ _ _).symm) leftRef rightRef
      let firstWeight := fun old : (CShape.product (ParameterShape N) shape).Value =>
        weight old.first old.second *
          conditionalProduct N count (fun index => outcomes index.succ) old.first
      let parameterRead : CInputRef (context base noQuantum N) (ParameterShape N) :=
        .storage (parameterRef base noQuantum N).toCStorageRef
      have firstMeasured : ∀ position,
          (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
            (CInputRef.product parameterRead observed).storageKeys := by
        intro position present
        exact (List.mem_append.mp present).elim
          (parameter_measured_separate base noQuantum N position) (measuredSeparate position)
      have firstWorking :
          (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
            (CInputRef.product parameterRead observed).storageKeys := by
        intro present
        exact (List.mem_append.mp present).elim
          (parameter_working_separate base noQuantum N) workingSeparate
      have firstSlot : (terminalRef base noQuantum N (indices 0)).key ∉
          (CInputRef.product parameterRead observed).storageKeys := by
        intro present
        exact (List.mem_append.mp present).elim
          (fun member => terminal_parameter_ne base noQuantum N (indices 0)
            (List.mem_singleton.mp member)) (slotSeparate 0)
      have firstLaw := nativeOracle_batch_reusedSample_reference base noQuantum N input
        (indices 0) (.product parameterRead observed) firstMeasured firstWorking firstSlot
        state firstWeight (outcomes 0) leftRef rightRef
      have reordered := reference_congr base noQuantum N advanced
        (fun store => tailWeight (store.read parameterRead) (store.read joint) *
          conditionalProduct N count (fun index => outcomes index.succ)
            (store.read parameterRead))
        (fun store => firstWeight (store.read (.product parameterRead observed)) *
          headIndicator (store.read (.storage head.toCStorageRef))) (fun store => by
        change (weight (store.read parameterRead) (store.read observed) *
          headIndicator (store.read (.storage head.toCStorageRef))) *
            conditionalProduct N count _ (store.read parameterRead) =
          (weight (store.read parameterRead) (store.read observed) *
            conditionalProduct N count _ (store.read parameterRead)) *
              headIndicator (store.read (.storage head.toCStorageRef))
        ring) leftRef rightRef
      have combined := reference_congr base noQuantum N state
        (fun store => firstWeight (store.read (.product parameterRead observed)) *
          ((selectedOutcomePMF (store.read (Native.liftInput (storageContext base N)
            (storage_empty base noQuantum N) N (parameter base N))) (outcomes 0)).toReal : ℂ))
        (fun store => weight (store.read parameterRead) (store.read observed) *
          conditionalProduct N (count + 1) outcomes (store.read parameterRead)) (fun store => by
        have readEqual := congrArg store.read
          (nativeOracle_batch_parameter_read base noQuantum N)
        change (weight (store.read parameterRead) (store.read observed) *
          conditionalProduct N count _ (store.read parameterRead)) * _ = _
        rw [readEqual]
        exact conditionalProduct_step N count outcomes (store.read parameterRead)
          (weight (store.read parameterRead) (store.read observed))) leftRef rightRef
      exact (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef).trans (aligned.trans (tailLaw.trans
          (reordered.trans (firstLaw.trans combined))))

/-- Sixteen actual reset/member/pack stages have the joint law of their real common parameter. -/
theorem nativeOracle_batch_reusedTerminals_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Circuit.forRange 16 (reusedSample base noQuantum N input)).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        ∏ index : Fin 16, ((selectedOutcomePMF
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)).toReal : ℂ)) leftRef rightRef := by
  let observed := CInputRef.storage (sourceRef base noQuantum N).toCStorageRef
  have measuredSeparate := source_measured_separate base noQuantum N
  have workingSeparate := source_working_separate base noQuantum N
  have slotsSeparate : ∀ index : Fin 16,
      (terminalRef base noQuantum N index).key ∉ observed.storageKeys :=
    fun index member => terminal_source_ne base noQuantum N index (List.mem_singleton.mp member)
  exact range_reference base noQuantum N input 16 id Function.injective_id observed
    measuredSeparate workingSeparate slotsSeparate state weight outcomes leftRef rightRef

/-- The first actual member and its fifteen paid successors have the same joint source law. -/
theorem nativeOracle_batch_firstTerminals_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((firstBatch base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        ∏ index : Fin 16, ((selectedOutcomePMF
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)).toReal : ℂ)) leftRef rightRef := by
  let count := 15
  let indices : Fin 16 → Fin 16 := id
  have distinct : Function.Injective indices := Function.injective_id
  let shape := CShape.bits (residueSamplingBits N)
  let observed : CInputRef (context base noQuantum N) shape :=
    .storage (sourceRef base noQuantum N).toCStorageRef
  have measuredSeparate := source_measured_separate base noQuantum N
  have workingSeparate := source_working_separate base noQuantum N
  have slotSeparate : ∀ index : Fin 16,
      (terminalRef base noQuantum N (indices index)).key ∉ observed.storageKeys :=
    fun index member => terminal_source_ne base noQuantum N index (List.mem_singleton.mp member)
  let head := terminalRef base noQuantum N (indices 0)
  let joint : CInputRef (context base noQuantum N)
      (.product shape (.bits (measurementBits N))) :=
    .product observed (.storage head.toCStorageRef)
  let first := (body (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).seq (copy base noQuantum N (indices 0))
  let rest := Circuit.forRange count fun index =>
    reusedSample base noQuantum N input (indices index.succ)
  let advanced := first.execute Reference state
  let headIndicator := fun value : (CShape.bits (measurementBits N)).Value =>
    if value = CShape.Value.bits (outcomes 0) then (1 : ℂ) else 0
  let tailWeight := fun parameter : (ParameterShape N).Value =>
    fun old : (CShape.product shape (.bits (measurementBits N))).Value =>
      weight parameter old.first * headIndicator old.second
  have tailDistinct : Function.Injective (fun index : Fin count => indices index.succ) :=
    fun _ _ same => Fin.succ_injective _ (distinct same)
  have tailMeasured : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        joint.storageKeys := by
    intro position present
    exact (List.mem_append.mp present).elim (measuredSeparate position)
      (terminal_measured_separate base noQuantum N position (indices 0))
  have tailWorking :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        joint.storageKeys := by
    intro present
    exact (List.mem_append.mp present).elim workingSeparate
      (terminal_working_separate base noQuantum N (indices 0))
  have tailSlots : ∀ index : Fin count,
      (terminalRef base noQuantum N (indices index.succ)).key ∉ joint.storageKeys := by
    intro index present
    rcases List.mem_append.mp present with original | headKey
    · exact slotSeparate index.succ original
    · have same := nativeOracle_batch_terminal_keys base noQuantum N
        (List.mem_singleton.mp headKey)
      have impossible := congrArg Fin.val (distinct same)
      simp only [Fin.val_succ, Fin.val_zero] at impossible
      omega
  have tailLaw := range_reference base noQuantum N input count
    (fun index => indices index.succ) tailDistinct joint
    tailMeasured tailWorking tailSlots advanced tailWeight (fun index => outcomes index.succ)
    leftRef rightRef
  let finalWeight := fun store : Store (context base noQuantum N) =>
    weight (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read observed) *
      terminalIndicator base noQuantum N (count + 1) indices outcomes store
  have aligned := reference_congr base noQuantum N (rest.execute Reference advanced)
    finalWeight (fun store => tailWeight
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read joint) * terminalIndicator base noQuantum N count
        (fun index => indices index.succ) (fun index => outcomes index.succ) store)
    (fun store => by
      change weight _ _ * terminalIndicator base noQuantum N (count + 1)
        indices outcomes store =
        (weight _ _ * headIndicator (store.read (.storage head.toCStorageRef))) *
          terminalIndicator base noQuantum N count
            (fun index => indices index.succ) (fun index => outcomes index.succ) store
      rw [terminalIndicator, Fin.prod_univ_succ]
      exact (mul_assoc _ _ _).symm) leftRef rightRef
  let firstWeight := fun old : (CShape.product (ParameterShape N) shape).Value =>
    weight old.first old.second *
      conditionalProduct N count (fun index => outcomes index.succ) old.first
  let parameterRead : CInputRef (context base noQuantum N) (ParameterShape N) :=
    .storage (parameterRef base noQuantum N).toCStorageRef
  have firstMeasured : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        (CInputRef.product parameterRead observed).storageKeys := by
    intro position present
    exact (List.mem_append.mp present).elim
      (parameter_measured_separate base noQuantum N position) (measuredSeparate position)
  have firstWorking :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        (CInputRef.product parameterRead observed).storageKeys := by
    intro present
    exact (List.mem_append.mp present).elim
      (parameter_working_separate base noQuantum N) workingSeparate
  have firstSlot : (terminalRef base noQuantum N (indices 0)).key ∉
      (CInputRef.product parameterRead observed).storageKeys := by
    intro present
    exact (List.mem_append.mp present).elim
      (fun member => terminal_parameter_ne base noQuantum N (indices 0)
        (List.mem_singleton.mp member)) (slotSeparate 0)
  have firstLaw := nativeOracle_batch_firstSample_reference base noQuantum N input
    (indices 0) (.product parameterRead observed) firstMeasured firstWorking firstSlot
    state seeded firstWeight (outcomes 0) leftRef rightRef
  have reordered := reference_congr base noQuantum N advanced
    (fun store => tailWeight (store.read parameterRead) (store.read joint) *
      conditionalProduct N count (fun index => outcomes index.succ)
        (store.read parameterRead))
    (fun store => firstWeight (store.read (.product parameterRead observed)) *
      headIndicator (store.read (.storage head.toCStorageRef))) (fun store => by
    change (weight (store.read parameterRead) (store.read observed) *
      headIndicator (store.read (.storage head.toCStorageRef))) *
        conditionalProduct N count _ (store.read parameterRead) =
      (weight (store.read parameterRead) (store.read observed) *
        conditionalProduct N count _ (store.read parameterRead)) *
          headIndicator (store.read (.storage head.toCStorageRef))
    ring) leftRef rightRef
  have combined := reference_congr base noQuantum N state
    (fun store => firstWeight (store.read (.product parameterRead observed)) *
      ((selectedOutcomePMF (store.read (Native.liftInput (storageContext base N)
        (storage_empty base noQuantum N) N (parameter base N))) (outcomes 0)).toReal : ℂ))
    (fun store => weight (store.read parameterRead) (store.read observed) *
      conditionalProduct N (count + 1) outcomes (store.read parameterRead)) (fun store => by
    have readEqual := congrArg store.read
      (nativeOracle_batch_parameter_read base noQuantum N)
    change (weight (store.read parameterRead) (store.read observed) *
      conditionalProduct N count _ (store.read parameterRead)) * _ = _
    rw [readEqual]
    exact conditionalProduct_step N count outcomes (store.read parameterRead)
      (weight (store.read parameterRead) (store.read observed))) leftRef rightRef
  exact (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
    leftRef rightRef).trans (aligned.trans (tailLaw.trans
      (reordered.trans (firstLaw.trans combined))))


attribute [local irreducible] Slots.allocateSamples Slots.liftSamples
  ShorStyle.Canonical.Sampler.Program.circuit ShorStyle.Canonical.Sampler.Program.step
  ShorStyle.Canonical.Sampler.Retained.circuit

private theorem fixedSlots_pair_reference {ctx : RuntimeCtx .quantum}
    {firstShape secondShape : CShape}
    (N : Nat) (first : CWriteRef ctx firstShape) (second : CWriteRef ctx secondShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : firstShape.Value → secondShape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((Slots.allocate ctx N).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Slots.liftWrite N first).toCStorageRef))
        (entry.1.read (.storage (Slots.liftWrite N second).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight
        (entry.1.read (.storage first.toCStorageRef))
        (entry.1.read (.storage second.toCStorageRef))) leftRef rightRef := by
  let oldRead := CInputRef.product (.storage first.toCStorageRef) (.storage second.toCStorageRef)
  let oldWeight := fun value : (CShape.product firstShape secondShape).Value =>
    weight value.first value.second
  let previous := Slots.allocateSamples ctx (measurementBits N) 16
  let middle := Slots.samples ctx (measurementBits N) 16
  let factor := Circuit.retain middle middle.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) middle.canonicalFreshKey_fresh
  have lifted : slotsInput (measurementBits N) oldRead 16 =
      .product (.storage (Slots.liftSamples (measurementBits N) first 16).toCStorageRef)
        (.storage (Slots.liftSamples (measurementBits N) second 16).toCStorageRef) :=
    (slotsInput_product (measurementBits N) _ _ 16).trans
      (congrArg₂ CInputRef.product (slotsInput_storage _ first 16)
        (slotsInput_storage _ second 16))
  have kept := Circuit.referenceFiberSum_execute_retain_input
    (.product (.storage (Slots.liftSamples (measurementBits N) first 16).toCStorageRef)
      (.storage (Slots.liftSamples (measurementBits N) second 16).toCStorageRef))
    middle.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
    middle.canonicalFreshKey_fresh (previous.execute Reference state) oldWeight leftRef rightRef
  have oldSlots := slots_reference (measurementBits N) oldRead 16 state oldWeight leftRef rightRef
  have observed := congrArg
    (fun read : CInputRef middle (.product firstShape secondShape) =>
      ExecutionState.referenceFiberSum (previous.execute Reference state)
        (fun entry _ => oldWeight (entry.1.read read)) leftRef rightRef) lifted
  exact (Circuit.referenceFiberSum_execute_seq previous factor state
    (fun store => weight (store.read (.storage (Slots.liftWrite N first).toCStorageRef))
      (store.read (.storage (Slots.liftWrite N second).toCStorageRef))) leftRef rightRef).trans
        (kept.trans (observed.symm.trans oldSlots))

private theorem initialized_input_reference {shape : CShape}
    (parameter : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Native.allocate base noQuantum N).execute Reference
        ((Native.prepare base noQuantum N).execute Reference state))
      (fun entry _ => weight (entry.1.read (Native.liftInput base noQuantum N parameter)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read parameter))
        leftRef rightRef := by
  let prepared := (Native.prepare base noQuantum N).execute Reference state
  let prior := MeasurementCells.liftInput 2 (Native.bankInput base noQuantum N parameter)
    (measurementBits N)
  let retention := Circuit.retain (Native.cellsContext base noQuantum N)
    (Native.cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh
  have split := Circuit.referenceFiberSum_execute_seq
    (MeasurementCells.allocate (Native.bankContext base noQuantum N) 2 (measurementBits N))
    retention
    prepared (fun store => weight (store.read (Native.liftInput base noQuantum N parameter)))
    leftRef rightRef
  have retained := Circuit.referenceFiberSum_execute_retain_input prior
    (Native.cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh
    ((MeasurementCells.allocate (Native.bankContext base noQuantum N) 2 (measurementBits N)).execute
      Reference prepared) weight leftRef rightRef
  have cellsPreserved := MeasurementCells.allocate_referenceFiberSum_input
    (Native.bankInput base noQuantum N parameter) 2 (measurementBits N)
    prepared weight leftRef rightRef
  have preparationPreserved := Circuit.referenceFiberSum_execute_prepare_input parameter
    base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N) (preparation N) state weight leftRef rightRef
  exact split.trans (retained.trans (cellsPreserved.trans preparationPreserved))

private theorem lifted_product {left right : CShape}
    (first : CInputRef base left) (second : CInputRef base right) :
    Native.liftInput base noQuantum N (.product first second) =
      .product (Native.liftInput base noQuantum N first)
        (Native.liftInput base noQuantum N second) := by
  exact congrArg
    (fun read : CInputRef (cellsContext base noQuantum N) (.product left right) =>
      read.underRetained (cellsContext base noQuantum N).canonicalFreshKey
        (.bits (measurementBits N)) (cellsContext base noQuantum N).canonicalFreshKey_fresh)
    (MeasurementCells.liftInput_product 2 (bankInput base noQuantum N first)
      (bankInput base noQuantum N second) (measurementBits N))

private theorem setup_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel
      ((setup base noQuantum N).execute Reference state) := by
  apply BasisSeeded.seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    ((Slots.allocate (sourceContext base N) N).seq
      ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
        (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)))
  apply BasisSeeded.seq (Slots.allocate (sourceContext base N) N)
    ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
      (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N))
  apply BasisSeeded.seq
    (Native.prepare (storageContext base N) (storage_empty base noQuantum N) N)
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)
  exact nativeOracle_initial_seeded (storageContext base N) (storage_empty base noQuantum N) N _

/-- The actual setup retains the full original parameter/source uniform mixture and Reference. -/
theorem nativeOracle_batch_setup_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((setup base noQuantum N).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
        leftRef rightRef := by
  let sampled := ShorStyle.Canonical.Sampler.Retained.circuit base N
  let storage := Slots.allocate (sourceContext base N) N
  let initialized := (Native.prepare (storageContext base N)
    (storage_empty base noQuantum N) N).seq
      (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)
  let initialState := storage.execute Reference (sampled.execute Reference state)
  let oldParameter := Slots.liftWrite N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
  let oldSource := Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)
  let pair : CInputRef (storageContext base N)
      (.product (ParameterShape N) (.bits (residueSamplingBits N))) :=
    .product (.storage oldParameter.toCStorageRef) (.storage oldSource.toCStorageRef)
  let pairWeight := fun value : (CShape.product (ParameterShape N)
      (.bits (residueSamplingBits N))).Value => weight value.first value.second
  let observe := fun store : Store (context base noQuantum N) => weight
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
  have lifted := (lifted_product (storageContext base N) (storage_empty base noQuantum N) N
    (.storage oldParameter.toCStorageRef) (.storage oldSource.toCStorageRef)).trans
      (congrArg₂ CInputRef.product (underBank_read base noQuantum N oldParameter)
        (underBank_read base noQuantum N oldSource))
  have aligned := congrArg
    (fun read : CInputRef (context base noQuantum N)
        (.product (ParameterShape N) (.bits (residueSamplingBits N))) =>
      ExecutionState.referenceFiberSum (initialized.execute Reference initialState)
        (fun entry _ => pairWeight (entry.1.read read)) leftRef rightRef) lifted
  have beforeBank := (Circuit.referenceFiberSum_execute_seq
    (Native.prepare (storageContext base N) (storage_empty base noQuantum N) N)
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)
    initialState (fun store => pairWeight (store.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N pair)))
    leftRef rightRef).trans
      (initialized_input_reference (storageContext base N) (storage_empty base noQuantum N) N
        pair initialState pairWeight leftRef rightRef)
  have beforeSlots := fixedSlots_pair_reference N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)
    (sampled.execute Reference state) weight leftRef rightRef
  have original := ShorStyle.Canonical.Sampler.Retained.samplerRetained_parameter_sample_reference
    input.samplerInput state weight leftRef rightRef
  exact (Circuit.referenceFiberSum_execute_seq sampled (storage.seq initialized)
    state observe leftRef rightRef).trans
      ((Circuit.referenceFiberSum_execute_seq storage initialized
        (sampled.execute Reference state) observe leftRef rightRef).trans
          (aligned.symm.trans (beforeBank.trans (beforeSlots.trans original))))


private theorem parameter_source_ne :
    (parameterRef base noQuantum N).key ≠ (sourceRef base noQuantum N).key := by
  intro same
  have parameterKey := (nativeOracle_underBank_key base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))).trans
      (liftedSamples_key (measurementBits N)
        (ShorStyle.Canonical.Sampler.Retained.parameterRef base N) 16)
  have sourceKey := (nativeOracle_underBank_key base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))).trans
      (liftedSamples_key (measurementBits N)
        (ShorStyle.Canonical.Sampler.Retained.sampleRef base N) 16)
  exact ShorStyle.Canonical.Sampler.Retained.samplerRetained_parameter_key_ne_sample base N
    ((parameterKey.symm.trans same).trans sourceKey)

private theorem redraw_weight (input : Input N) (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ) :
    weight ((redrawStep base noQuantum N store value).1.read
        (.storage (parameterRef base noQuantum N).toCStorageRef))
      ((redrawStep base noQuantum N store value).1.read
        (.storage (sourceRef base noQuantum N).toCStorageRef)) =
      weight (parameterValue input value)
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) := by
  have actual := congrArg (fun result : Store (context base noQuantum N) => weight
    (result.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (result.read (.storage (sourceRef base noQuantum N).toCStorageRef)))
      (nativeOracle_batch_redraw_store base noQuantum N input store value)
  refine actual.trans ?_
  apply congrArg₂ weight
  · exact Store.read_write_same _ _ _
  · exact (Store.read_write_other _ (parameterRef base noQuantum N)
      (sourceRef base noQuantum N).toCStorageRef _ (parameter_source_ne base noQuantum N)).trans
        (Store.read_write_same _ _ _)

/-- Redraw uses one actual uniform source for both cells and preserves full Reference. -/
theorem nativeOracle_batch_redraw_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((redraw base noQuantum N).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
        leftRef rightRef := by
  let count : ℕ+ := ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
  let update := fun entry : (Store (context base noQuantum N) × History) × Fin count =>
    ((redrawStep base noQuantum N entry.1.1 entry.2).1,
      (entry.1.2, (redrawStep base noQuantum N entry.1.1 entry.2).2))
  let observe := fun store : Store (context base noQuantum N) => weight
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        (History × (redraw base noQuantum N).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) leftRef rightRef)
    (nativeOracle_batch_redraw_execute base noQuantum N Reference state)
  have pushed := ExecutionState.referenceFiberSum_mapClassical (uniformChoice state count)
    update (fun entry _ => observe entry.1) leftRef rightRef
  have sampled := referenceFiberSum_uniformChoice state count
    (fun entry _ => observe (update entry).1) leftRef rightRef
  have coefficient : (((count : ℝ)⁻¹ : ℝ) : ℂ) =
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) := by
    rw [Complex.ofReal_inv]
    exact congrArg (fun number : ℝ => (number : ℂ)⁻¹)
      (show (count : ℝ) = ((2 ^ residueSamplingBits N : Nat) : ℝ) from rfl)
  refine executed.trans (pushed.trans (sampled.trans ?_))
  apply congrArg
    (fun read : (Store (context base noQuantum N) × History) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state read leftRef rightRef)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  exact congrArg₂ HMul.hMul coefficient (redraw_weight base noQuantum N input entry.1 value weight)

attribute [local irreducible] setup firstBatch redraw reusedSample code nextBatch

/-- The full first batch uses the actual initial source draw and all sixteen actual samples. -/
theorem nativeOracle_batch_code_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) *
                ∏ index : Fin 16,
                  ((selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal : ℂ)))
        leftRef rightRef := by
  unfold code
  let observe := fun store : Store (context base noQuantum N) => weight
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
      terminalIndicator base noQuantum N 16 id outcomes store
  have sampled := nativeOracle_batch_firstTerminals_reference base noQuantum N input
    ((setup base noQuantum N).execute Reference state)
    (setup_seeded base noQuantum N state) weight outcomes leftRef rightRef
  have source := nativeOracle_batch_setup_reference base noQuantum N input state
    (fun parameter source => weight parameter source *
      ∏ index : Fin 16, ((selectedOutcomePMF (N := N) parameter (outcomes index)).toReal : ℂ))
    leftRef rightRef
  have sequence := Circuit.referenceFiberSum_execute_seq (setup base noQuantum N)
    (firstBatch base noQuantum N input) state observe leftRef rightRef
  exact sequence.trans (sampled.trans source)

/-- Every later real batch redraws once and uses its sixteen paid reset/member/pack stages. -/
theorem nativeOracle_batch_next_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((nextBatch base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) *
                ∏ index : Fin 16,
                  ((selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal : ℂ)))
        leftRef rightRef := by
  unfold nextBatch
  let observe := fun store : Store (context base noQuantum N) => weight
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
      terminalIndicator base noQuantum N 16 id outcomes store
  have sampled := nativeOracle_batch_reusedTerminals_reference base noQuantum N input
    ((redraw base noQuantum N).execute Reference state) weight outcomes leftRef rightRef
  have source := nativeOracle_batch_redraw_reference base noQuantum N input state
    (fun parameter source => weight parameter source *
      ∏ index : Fin 16, ((selectedOutcomePMF (N := N) parameter (outcomes index)).toReal : ℂ))
    leftRef rightRef
  have sequence := Circuit.referenceFiberSum_execute_seq (redraw base noQuantum N)
    (Circuit.forRange 16 (reusedSample base noQuantum N input)) state observe leftRef rightRef
  exact sequence.trans (sampled.trans source)

private theorem vector_indicator (length width : Nat)
    (values : Fin length → (CShape.bits width).Value)
    (outcomes : Fin length → Fin width → Bool) :
    (if CShape.Value.fixedVector values =
      CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
      then (1 : ℂ) else 0) =
      ∏ index : Fin length,
        if values index = CShape.Value.bits (outcomes index) then 1 else 0 := by
  classical
  by_cases allEqual : ∀ index, values index = CShape.Value.bits (outcomes index)
  · have equal := congrArg CShape.Value.fixedVector (funext allEqual)
    simp only [equal, if_true, allEqual, Finset.prod_const_one]
  · obtain ⟨index, different⟩ := not_forall.mp allEqual
    have differentVector : CShape.Value.fixedVector values ≠
        CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index)) :=
      fun equal => different (congrFun (CShape.Value.fixedVector.inj equal) index)
    rw [if_neg differentVector]
    exact (Finset.prod_eq_zero (Finset.mem_univ index) (if_neg different)).symm

private theorem source_probability_cast (input : Input N)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) :
    (∑ value : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        (∏ index : Fin 16,
          ((selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal : ℂ))) =
      ((∑ value : Fin (2 ^ residueSamplingBits N),
        ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
          ∏ index : Fin 16,
            (selectedOutcomePMF (parameterValue input value)
              (outcomes index)).toReal : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv]

/-- The declared sixteen-cell output has the same source-mixture probability on every input. -/
theorem nativeOracle_batch_outputDistribution (input : Input N) {Reference : Register}
    (original : Execution.Input base Reference)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) :
    (run base noQuantum N input).outputDistribution original
        (.fixedVector fun index => .bits (outcomes index)) =
      ENNReal.ofReal (∑ value : Fin (2 ^ residueSamplingBits N),
        ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
          ∏ index : Fin 16,
            (selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal) := by
  let actual := run base noQuantum N input
  let read := fun record : actual.Record => actual.result record
  let probability : ℝ := ∑ value : Fin (2 ^ residueSamplingBits N),
    ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
      ∏ index : Fin 16,
        (selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal
  have mapped := congrArg
    (fun distribution : PMF (CShape.Value (.fixedVector 16 (.bits (measurementBits N)))) =>
      distribution (.fixedVector fun index => .bits (outcomes index)))
    (ExecutionState.toPMF_mapClassical (actual.execute Reference original.state)
      (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply, ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  have full : (∑ reference : Reference.Index,
      ExecutionState.referenceFiberSum (actual.execute Reference original.state)
        (fun entry _ => if read entry =
          CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
          then 1 else 0) reference reference) = (probability : ℂ) := by
    have entries : ∀ reference : Reference.Index,
        ExecutionState.referenceFiberSum (actual.execute Reference original.state)
          (fun entry _ => if read entry =
            CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
            then 1 else 0) reference reference =
          ExecutionState.referenceFiberSum original.state (fun _ _ => (probability : ℂ))
            reference reference := by
      intro reference
      have aligned := congrArg
        (fun observe : actual.Record → (context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum (actual.execute Reference original.state)
            observe reference reference)
        (funext fun entry => funext fun _ => vector_indicator 16 (measurementBits N)
          (fun index => entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef))
          outcomes)
      have law := nativeOracle_batch_code_reference base noQuantum N input
        (original.state.mapClassical (fun store => (store, store)))
        (fun _ _ => 1) outcomes reference reference
      have scalar := congrArg
        (fun coefficient : ℂ => ExecutionState.referenceFiberSum original.state
          (fun _ _ => coefficient) reference reference)
        (source_probability_cast N input outcomes)
      simp only [one_mul] at law
      exact aligned.trans (law.trans
        ((ExecutionState.referenceFiberSum_mapClassical original.state
          (fun store => (store, store)) _ reference reference).trans scalar))
    have summed := (Finset.sum_congr rfl (fun reference _ => entries reference)).trans
      (ExecutionState.referenceFiberSum_sum_constant original.state (probability : ℂ))
    have normalized : original.state.mass = 1 := original.normalized
    simpa only [normalized, Complex.ofReal_one, mul_one] using summed
  exact (congrArg Complex.re full).trans (Complex.ofReal_re probability)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
