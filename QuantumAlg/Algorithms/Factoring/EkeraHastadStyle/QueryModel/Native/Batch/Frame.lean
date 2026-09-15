/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# Earlier classical observations in actual fixed-bank batch laws

The measured batch preserves each structural read outside its real write
slots. The complete weighted reference law keeps that earlier read jointly
with the actual source, parameter and sixteen chronological samples. The
same real redraw and paid reset operations drive the later-batch law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem slotsInput_keys {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (observed : CInputRef ctx shape) (count : Nat) :
    (slotsInput width observed count).storageKeys = observed.storageKeys := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (CInputRef.storageKeys_underRetained _ _ _ _).trans ih

private theorem sample_not_mem_input {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (observed : CInputRef ctx shape) (count : Nat) (index : Fin count) :
    (Slots.sampleRef ctx width count index).key ∉
      (slotsInput width observed count).storageKeys := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · exact CInputRef.fresh_not_mem_storageKeys_underRetained
          (slotsInput width observed count) (Slots.samples ctx width count).canonicalFreshKey
          (.bits width) (Slots.samples ctx width count).canonicalFreshKey_fresh
      · change (Slots.sampleRef ctx width count previous).key ∉
          ((slotsInput width observed count).underRetained
            (Slots.samples ctx width count).canonicalFreshKey (.bits width)
            (Slots.samples ctx width count).canonicalFreshKey_fresh).storageKeys
        rw [CInputRef.storageKeys_underRetained]
        exact ih previous

attribute [local irreducible] Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- A structural earlier observation avoids exactly the fixed sampler's actual writes. -/
structure FrameSeparated {shape : CShape} (observed : CInputRef (context base noQuantum N) shape) :
    Prop where
  measured : ∀ position,
    (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
      observed.storageKeys
  working : (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
    observed.storageKeys
  slots : ∀ index, (terminalRef base noQuantum N index).key ∉ observed.storageKeys
  parameter : (parameterRef base noQuantum N).key ∉ observed.storageKeys
  source : (sourceRef base noQuantum N).key ∉ observed.storageKeys

/-- The first member and fifteen actual resets keep every protected earlier observation. -/
theorem nativeOracle_batch_firstTerminals_frame_reference (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (measuredFree : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingFree : (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      observed.storageKeys)
    (slotsFree : ∀ index, (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (weight : (ParameterShape N).Value → shape.Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((firstBatch base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read observed) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read observed) *
        ∏ index : Fin 16, ((selectedOutcomePMF
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)).toReal : ℂ)) leftRef rightRef := by
  let count := 15
  let indices : Fin 16 → Fin 16 := id
  have distinct : Function.Injective indices := Function.injective_id
  have measuredSeparate := measuredFree
  have workingSeparate := workingFree
  have slotSeparate : ∀ index : Fin 16,
      (terminalRef base noQuantum N (indices index)).key ∉ observed.storageKeys :=
    slotsFree
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

/-- Sixteen real paid samples keep the earlier read jointly with their unchanged source. -/
private theorem reused_frame (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separated : FrameSeparated base noQuantum N observed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.forRange 16 (reusedSample base noQuantum N input)).execute Reference state)
        (fun entry _ => weight (entry.1.read observed)
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
          terminalIndicator base noQuantum N 16 id outcomes entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read observed)
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        conditionalProduct N 16 outcomes
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))) left right := by
  let joint := CInputRef.product observed (.storage (sourceRef base noQuantum N).toCStorageRef)
  refine range_reference base noQuantum N input 16 id Function.injective_id joint ?_ ?_ ?_
    state (fun parameter old => weight old.first parameter old.second) outcomes left right
  · intro index present
    exact (List.mem_append.mp present).elim (separated.measured index)
      (source_measured_separate base noQuantum N index)
  · intro present
    exact (List.mem_append.mp present).elim separated.working
      (source_working_separate base noQuantum N)
  · intro index present
    exact (List.mem_append.mp present).elim (separated.slots index)
      (fun member => terminal_source_ne base noQuantum N index (List.mem_singleton.mp member))

attribute [local irreducible] ShorStyle.Canonical.Sampler.Program.circuit
  ShorStyle.Canonical.Sampler.Program.step

private theorem redraw_frame_read (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separated : FrameSeparated base noQuantum N observed)
    (store : Store (context base noQuantum N)) (value : Fin (2 ^ residueSamplingBits N)) :
    (redrawStep base noQuantum N store value).1.read observed = store.read observed := by
  have actual := congrArg (fun next : Store (context base noQuantum N) => next.read observed)
    (nativeOracle_batch_redraw_store base noQuantum N input store value)
  exact actual.trans ((Store.read_write_of_not_mem_storageKeys _ _ _ observed
    separated.parameter).trans
      (Store.read_write_of_not_mem_storageKeys _ _ _ observed separated.source))

private theorem redraw_frame (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separated : FrameSeparated base noQuantum N observed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((redraw base noQuantum N).execute Reference state)
        (fun entry _ => weight (entry.1.read observed)
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (entry.1.read observed) (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) left right := by
  let count : ℕ+ := ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
  let update := fun entry : (Store (context base noQuantum N) × History) × Fin count =>
    ((redrawStep base noQuantum N entry.1.1 entry.2).1,
      (entry.1.2, (redrawStep base noQuantum N entry.1.1 entry.2).2))
  let observe := fun store : Store (context base noQuantum N) => weight (store.read observed)
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        (History × (redraw base noQuantum N).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (nativeOracle_batch_redraw_execute base noQuantum N Reference state)
  have pushed := ExecutionState.referenceFiberSum_mapClassical (uniformChoice state count)
    update (fun entry _ => observe entry.1) left right
  have sampled := referenceFiberSum_uniformChoice state count
    (fun entry _ => observe (update entry).1) left right
  have coefficient : (((count : ℝ)⁻¹ : ℝ) : ℂ) =
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) := by
    rw [Complex.ofReal_inv]
    exact congrArg (fun number : ℝ => (number : ℂ)⁻¹)
      (show (count : ℝ) = ((2 ^ residueSamplingBits N : Nat) : ℝ) from rfl)
  refine executed.trans (pushed.trans (sampled.trans ?_))
  apply congrArg
    (fun read : (Store (context base noQuantum N) × History) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state read left right)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  apply congrArg₂ HMul.hMul coefficient
  dsimp only [observe, update]
  refine (congrArg (fun old => weight old _ _)
    (redraw_frame_read base noQuantum N input observed separated entry.1 value)).trans ?_
  exact redraw_weight base noQuantum N input entry.1 value (weight (entry.1.read observed))

private theorem next_frame_samples (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separated : FrameSeparated base noQuantum N observed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((nextBatch base noQuantum N input).execute Reference state)
        (fun entry _ => weight (entry.1.read observed)
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
          terminalIndicator base noQuantum N 16 id outcomes entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ source : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (entry.1.read observed) (parameterValue input source)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source)) *
              conditionalProduct N 16 outcomes (parameterValue input source))) left right := by
  let first := redraw base noQuantum N
  let rest := Circuit.forRange 16 (reusedSample base noQuantum N input)
  let observe := fun store : Store (context base noQuantum N) => weight (store.read observed)
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
      terminalIndicator base noQuantum N 16 id outcomes store
  have later := reused_frame base noQuantum N input observed separated
    (first.execute Reference state) weight outcomes left right
  have drawn := redraw_frame base noQuantum N input observed separated state
    (fun old parameter source => weight old parameter source *
      conditionalProduct N 16 outcomes parameter) left right
  exact (Circuit.referenceFiberSum_execute_seq first rest state observe left right).trans
    (later.trans drawn)

private def fixedInput {ctx : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (observed : CInputRef ctx shape) : CInputRef (Slots.context ctx N) shape :=
  (slotsInput (measurementBits N) observed 16).underRetained
    (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey_fresh

private theorem fixedInput_product {ctx : RuntimeCtx .quantum} {left right : CShape}
    (N : Nat) (first : CInputRef ctx left) (second : CInputRef ctx right) :
    fixedInput N (.product first second) =
      .product (fixedInput N first) (fixedInput N second) :=
  congrArg
    (fun read : CInputRef (Slots.samples ctx (measurementBits N) 16) (.product left right) =>
      read.underRetained (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey_fresh)
    (slotsInput_product (measurementBits N) first second 16)

private theorem fixedInput_storage {ctx : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (ref : CWriteRef ctx shape) :
    fixedInput N (.storage ref.toCStorageRef) =
      .storage (Slots.liftWrite N ref).toCStorageRef :=
  congrArg
    (fun read : CInputRef (Slots.samples ctx (measurementBits N) 16) shape =>
      read.underRetained (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Slots.samples ctx (measurementBits N) 16).canonicalFreshKey_fresh)
    (slotsInput_storage (measurementBits N) ref 16)

private theorem fixedInput_reference {ctx : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : shape.Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((Slots.allocate ctx N).execute Reference state)
      (fun entry _ => weight (entry.1.read (fixedInput N observed))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read observed)) left right := by
  let previous := Slots.allocateSamples ctx (measurementBits N) 16
  let middle := Slots.samples ctx (measurementBits N) 16
  let finalCell := Circuit.retain middle middle.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) middle.canonicalFreshKey_fresh
  exact (Circuit.referenceFiberSum_execute_seq previous finalCell state
    (fun store => weight (store.read (fixedInput N observed))) left right).trans
      ((Circuit.referenceFiberSum_execute_retain_input
        (slotsInput (measurementBits N) observed 16) middle.canonicalFreshKey
        (.option (.unsignedWord (modulusBits N))) middle.canonicalFreshKey_fresh
        (previous.execute Reference state) weight left right).trans
          (slots_reference (measurementBits N) observed 16 state weight left right))

/-- The same earlier structural read under the actual source, slots, bank and readout cells. -/
def callerInput {shape : CShape} (observed : CInputRef base shape) :
    CInputRef (context base noQuantum N) shape :=
  Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
    (fixedInput N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed))

/-- Actual initialization retains the joint old input, newly drawn source and derived parameter. -/
theorem nativeOracle_batch_setup_input_reference (input : Input N)
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((setup base noQuantum N).execute Reference state)
      (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (entry.1.read observed) (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) left right := by
  let sampled := ShorStyle.Canonical.Sampler.Retained.circuit base N
  let storage := Slots.allocate (sourceContext base N) N
  let initialized := (Native.prepare (storageContext base N)
    (storage_empty base noQuantum N) N).seq
      (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)
  let originalRead : CInputRef (sourceContext base N)
      (.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))) :=
    .product (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed)
      (.product (.storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef)
        (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef))
  let oldRead := fixedInput N originalRead
  let readWeight := fun value :
      (CShape.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))).Value =>
    weight value.first value.second.first value.second.second
  let initialState := storage.execute Reference (sampled.execute Reference state)
  let finalRead : CInputRef (context base noQuantum N)
      (.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))) :=
    .product (callerInput base noQuantum N observed)
      (.product (.storage (parameterRef base noQuantum N).toCStorageRef)
        (.storage (sourceRef base noQuantum N).toCStorageRef))
  let observe := fun store : Store (context base noQuantum N) => readWeight (store.read finalRead)
  have lifted : Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      oldRead = finalRead := by
    let oldCaller := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
    let oldParameter := ShorStyle.Canonical.Sampler.Retained.parameterRef base N
    let oldSource := ShorStyle.Canonical.Sampler.Retained.sampleRef base N
    have fixedPair := (fixedInput_product N (.storage oldParameter.toCStorageRef)
      (.storage oldSource.toCStorageRef)).trans
        (congrArg₂ CInputRef.product (fixedInput_storage N oldParameter)
          (fixedInput_storage N oldSource))
    have fixedTriple := (fixedInput_product N oldCaller
      (.product (.storage oldParameter.toCStorageRef)
        (.storage oldSource.toCStorageRef))).trans
          (congrArg (CInputRef.product (fixedInput N oldCaller)) fixedPair)
    have firstLift := congrArg
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N) fixedTriple
    have secondLift := lifted_product (storageContext base N) (storage_empty base noQuantum N) N
      (fixedInput N oldCaller)
      (.product (.storage (Slots.liftWrite N oldParameter).toCStorageRef)
        (.storage (Slots.liftWrite N oldSource).toCStorageRef))
    have pairLift := (lifted_product (storageContext base N) (storage_empty base noQuantum N) N
      (.storage (Slots.liftWrite N oldParameter).toCStorageRef)
      (.storage (Slots.liftWrite N oldSource).toCStorageRef)).trans
        (congrArg₂ CInputRef.product
          (underBank_read base noQuantum N (Slots.liftWrite N oldParameter))
          (underBank_read base noQuantum N (Slots.liftWrite N oldSource)))
    exact firstLift.trans (secondLift.trans
      (congrArg (CInputRef.product (callerInput base noQuantum N observed)) pairLift))
  have aligned := congrArg
    (fun read : CInputRef (context base noQuantum N)
        (.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))) =>
      ExecutionState.referenceFiberSum (initialized.execute Reference initialState)
        (fun entry _ => readWeight (entry.1.read read)) left right) lifted
  have beforeBank := (Circuit.referenceFiberSum_execute_seq
    (Native.prepare (storageContext base N) (storage_empty base noQuantum N) N)
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)
    initialState (fun store => readWeight (store.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N oldRead)))
    left right).trans
      (initialized_input_reference (storageContext base N) (storage_empty base noQuantum N) N
        oldRead initialState readWeight left right)
  have beforeSlots := fixedInput_reference N originalRead
    (sampled.execute Reference state) readWeight left right
  have original := ShorStyle.Canonical.Sampler.Retained.samplerRetained_reference_input
    input.samplerInput observed state weight left right
  exact (Circuit.referenceFiberSum_execute_seq sampled (storage.seq initialized)
    state observe left right).trans
      ((Circuit.referenceFiberSum_execute_seq storage initialized
        (sampled.execute Reference state) observe left right).trans
          (aligned.symm.trans (beforeBank.trans (beforeSlots.trans original))))

private theorem fixedInput_keys {ctx : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (observed : CInputRef ctx shape) :
    (fixedInput N observed).storageKeys = observed.storageKeys :=
  (CInputRef.storageKeys_underRetained _ _ _ _).trans
    (slotsInput_keys (measurementBits N) observed 16)

private theorem fixedWrite_key {ctx : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (ref : CWriteRef ctx shape) : (Slots.liftWrite N ref).key = ref.key := by
  have same := (congrArg CInputRef.storageKeys (fixedInput_storage N ref)).symm.trans
    (fixedInput_keys N (.storage ref.toCStorageRef))
  exact List.singleton_inj.mp same

private theorem bankInput_keys {shape : CShape} (observed : CInputRef base shape) :
    (Native.bankInput base noQuantum N observed).storageKeys = observed.storageKeys := by
  induction observed with
  | storage ref => rfl
  | product first second firstIH secondIH => exact congrArg₂ List.append firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg List.flatten (congrArg List.ofFn (funext entriesIH))
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

private theorem nativeInput_keys {shape : CShape} (observed : CInputRef base shape) :
    (Native.liftInput base noQuantum N observed).storageKeys = observed.storageKeys :=
  (CInputRef.storageKeys_underRetained _ _ _ _).trans
    ((MeasurementCells.liftInput_storageKeys 2 (Native.bankInput base noQuantum N observed)
      (measurementBits N)).trans (bankInput_keys base noQuantum N observed))

/-- All five sampler write families are fresh relative to every original caller input. -/
theorem nativeOracle_batch_caller_separated {shape : CShape}
    (observed : CInputRef base shape) :
    FrameSeparated base noQuantum N (callerInput base noQuantum N observed) := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  let storedInput := fixedInput N sourceInput
  have finalKeys : (callerInput base noQuantum N observed).storageKeys =
      sourceInput.storageKeys :=
    (nativeInput_keys (storageContext base N) (storage_empty base noQuantum N) N storedInput).trans
      (fixedInput_keys N sourceInput)
  constructor
  · exact lifted_measured_separate base noQuantum N storedInput
  · exact lifted_working_separate base noQuantum N storedInput
  · intro index
    have oldAbsent := sample_not_mem_input (measurementBits N) sourceInput 16 index
    have oldKeys := slotsInput_keys (measurementBits N) sourceInput 16
    have oldResult : (Slots.terminalRef (sourceContext base N) N index).key ∉
        sourceInput.storageKeys :=
      (congrArg (fun keys =>
        (Slots.sampleRef (sourceContext base N) (measurementBits N) 16 index).key ∉ keys)
        oldKeys).mp oldAbsent
    exact (congrArg₂ (fun key keys => key ∉ keys)
      (nativeOracle_underBank_key base noQuantum N
        (Slots.terminalRef (sourceContext base N) N index)) finalKeys).mpr oldResult
  · have oldAbsent : (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).key ∉
        sourceInput.storageKeys :=
      CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _
    have keyEqual := (nativeOracle_underBank_key base noQuantum N
      (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))).trans
        (fixedWrite_key N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))
    exact (congrArg₂ (fun key keys => key ∉ keys) keyEqual finalKeys).mpr oldAbsent
  · let prior := observed.underRetained base.canonicalFreshKey (.bits (residueSamplingBits N))
      base.canonicalFreshKey_fresh
    have retainedKeys : sourceInput.storageKeys = prior.storageKeys :=
      CInputRef.storageKeys_underRetained _ _ _ _
    have oldAbsent : (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).key ∉
        sourceInput.storageKeys :=
      (congrArg (fun keys => base.canonicalFreshKey ∉ keys) retainedKeys).mpr
        (CInputRef.fresh_not_mem_storageKeys_underRetained observed base.canonicalFreshKey
          (.bits (residueSamplingBits N)) base.canonicalFreshKey_fresh)
    have keyEqual := (nativeOracle_underBank_key base noQuantum N
      (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))).trans
        (fixedWrite_key N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
    exact (congrArg₂ (fun key keys => key ∉ keys) keyEqual finalKeys).mpr oldAbsent

/-- The later recovery destination is also fresh relative to the complete caller observation. -/
theorem nativeOracle_batch_caller_factor_separate {shape : CShape}
    (observed : CInputRef base shape) :
    (factorRef base noQuantum N).key ∉ (callerInput base noQuantum N observed).storageKeys := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  have finalKeys := nativeInput_keys (storageContext base N) (storage_empty base noQuantum N) N
    (fixedInput N sourceInput)
  have oldAbsent : (Slots.factorRef (sourceContext base N) N).key ∉
      (fixedInput N sourceInput).storageKeys :=
    CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _
  exact (congrArg₂ (fun key keys => key ∉ keys)
    (nativeOracle_underBank_key base noQuantum N (Slots.factorRef (sourceContext base N) N))
    finalKeys).mpr oldAbsent

private theorem first_frame_samples (input : Input N)
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
          terminalIndicator base noQuantum N 16 id outcomes entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ source : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (entry.1.read observed) (parameterValue input source)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source)) *
                conditionalProduct N 16 outcomes (parameterValue input source))) left right := by
  let joint := CInputRef.product (callerInput base noQuantum N observed)
    (.storage (sourceRef base noQuantum N).toCStorageRef)
  have separated := nativeOracle_batch_caller_separated base noQuantum N observed
  have measuredFree : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        joint.storageKeys := by
    intro position present
    exact (List.mem_append.mp present).elim (separated.measured position)
      (source_measured_separate base noQuantum N position)
  have workingFree : (resultRef (storageContext base N)
      (storage_empty base noQuantum N) N).key ∉ joint.storageKeys := by
    intro present
    exact (List.mem_append.mp present).elim separated.working
      (source_working_separate base noQuantum N)
  have slotsFree : ∀ index, (terminalRef base noQuantum N index).key ∉ joint.storageKeys := by
    intro index present
    exact (List.mem_append.mp present).elim (separated.slots index)
      (fun present => terminal_source_ne base noQuantum N index (List.mem_singleton.mp present))
  let advanced := (setup base noQuantum N).execute Reference state
  let observe := fun store : Store (context base noQuantum N) =>
    weight (store.read (callerInput base noQuantum N observed))
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes store
  have sampled := nativeOracle_batch_firstTerminals_frame_reference base noQuantum N input
    joint measuredFree workingFree slotsFree advanced (setup_seeded base noQuantum N state)
    (fun parameter old => weight old.first parameter old.second) outcomes left right
  have drawn := nativeOracle_batch_setup_input_reference base noQuantum N input observed state
    (fun old parameter source => weight old parameter source *
      conditionalProduct N 16 outcomes parameter) left right
  exact (Circuit.referenceFiberSum_execute_seq (setup base noQuantum N)
    (firstBatch base noQuantum N input) state observe left right).trans (sampled.trans drawn)

/-- The real first setup and sixteen samples preserve the full earlier-input reference law. -/
theorem nativeOracle_batch_first_source_frame_reference (input : Input N)
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : shape.Value → (NativeBatch.resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N input).execute Reference state)
        (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
          (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) *
            weight (entry.1.read observed) output) left right := by
  let final := (code base noQuantum N input).execute Reference state
  have expanded := congrArg
    (fun observe : (Store (context base noQuantum N) ×
        (History × (code base noQuantum N input).Path)) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum final observe left right)
    (funext fun entry => funext fun _ => source_read_weight base noQuantum N entry.1
      (weight (entry.1.read (callerInput base noQuantum N observed))))
  have interchanged := reference_sum final
    (fun (samples : List.Vector (Fin (measurementBits N) → Bool) 16) entry _ =>
      weight (entry.1.read (callerInput base noQuantum N observed))
      (.product (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))
        (.product (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (.fixedVector fun index => .bits (samples.get index)))) *
            terminalIndicator base noQuantum N 16 id samples.get entry.1) left right
  refine expanded.trans (interchanged.trans ?_)
  have sampleLaws := Finset.sum_congr rfl
    (fun (samples : List.Vector (Fin (measurementBits N) → Bool) 16)
      (_ : samples ∈ Finset.univ) =>
      first_frame_samples base noQuantum N input observed state
        (fun old parameter source => weight old
          (.product source (.product parameter
            (.fixedVector fun index => .bits (samples.get index)))))
        samples.get left right)
  refine sampleLaws.trans ((reference_sum state _ left right).symm.trans ?_)
  apply congrArg
    (fun observe : (Store base × History) → base.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact source_moment N input (weight (entry.1.read observed))

attribute [local irreducible] context nextBatch

/-- The actual next source law is independent of a protected old read, in every reference entry. -/
theorem nativeOracle_batch_next_source_frame_reference (input : Input N)
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separated : FrameSeparated base noQuantum N observed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : shape.Value → (NativeBatch.resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((nextBatch base noQuantum N input).execute Reference state)
        (fun entry _ => weight (entry.1.read observed)
          (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) *
            weight (entry.1.read observed) output) left right := by
  let final := (nextBatch base noQuantum N input).execute Reference state
  have expanded := congrArg
    (fun observe : (Store (context base noQuantum N) ×
        (History × (nextBatch base noQuantum N input).Path)) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum final observe left right)
    (funext fun entry => funext fun _ =>
      source_read_weight base noQuantum N entry.1 (weight (entry.1.read observed)))
  refine expanded.trans ((reference_sum final _ left right).trans ?_)
  have sampleLaws := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun (samples : List.Vector (Fin (measurementBits N) → Bool) 16)
      (_ : samples ∈ Finset.univ) =>
      next_frame_samples base noQuantum N input observed separated state
        (fun old parameter source => weight old
          (.product source (.product parameter
            (.fixedVector fun index => .bits (samples.get index)))))
        samples.get left right)
  refine sampleLaws.trans ((reference_sum state _ left right).symm.trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) × History) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact source_moment N input (weight (entry.1.read observed))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
