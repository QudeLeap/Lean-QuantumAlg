/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Probability
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Caller
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Slots.Reference
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Initial
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference

/-!
# Initial seed and conditional law of the complete declared EH batch

The actual source sampler, fixed-slot allocation, quantum preparation and
working-cell allocation precede the first of sixteen physical observations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private theorem initialized_input_reference {shape : CShape}
    (observed : CInputRef (storageContext base N) shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (storageContext base N) Reference ((model input).HiddenState × History))
    (weight : shape.Value → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input).execute
        Reference ((Declared.prepare (storageContext base N)
          (storage_empty base noQuantum N) N input).execute Reference state))
      (fun entry _ => weight (entry.1.read
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N observed)))
        leftRef rightRef =
    ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read observed))
      leftRef rightRef := by
  let storage := storageContext base N
  let empty := storage_empty base noQuantum N
  let prepared := (Declared.prepare storage empty N input).execute Reference state
  let prior := MeasurementCells.liftInput 2 (Native.bankInput storage empty N observed)
    (measurementBits N)
  let retention := Circuit.retain (model := model input) (Native.cellsContext storage empty N)
    (Native.cellsContext storage empty N).canonicalFreshKey (.bits (measurementBits N))
    (Native.cellsContext storage empty N).canonicalFreshKey_fresh
  have split := Circuit.referenceFiberSum_execute_seq
    (MeasurementCells.allocate (model := model input)
      (Native.bankContext storage empty N) 2 (measurementBits N))
    retention prepared
    (fun store => weight (store.read (Native.liftInput storage empty N observed)))
    leftRef rightRef
  have retained := Circuit.referenceFiberSum_execute_retain_input
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model) (classicalOracles := .empty) prior
    (Native.cellsContext storage empty N).canonicalFreshKey (.bits (measurementBits N))
    (Native.cellsContext storage empty N).canonicalFreshKey_fresh
    ((MeasurementCells.allocate (model := model input)
      (Native.bankContext storage empty N) 2 (measurementBits N)).execute Reference prepared)
    weight leftRef rightRef
  have cellsPreserved := MeasurementCells.allocate_referenceFiberSum_input
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model) (classicalOracles := .empty)
    (Native.bankInput storage empty N observed) 2 (measurementBits N)
    prepared weight leftRef rightRef
  have preparationPreserved := Circuit.referenceFiberSum_execute_prepareZero_input
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model) (classicalOracles := .empty) observed
    storage.canonicalFreshKey (Native.layout N) storage.canonicalFreshKey_fresh
    (Native.allocationDisjoint storage empty N) state weight leftRef rightRef
  exact split.trans (retained.trans (cellsPreserved.trans preparationPreserved))

private theorem lifted_product {left right : CShape}
    (first : CInputRef (storageContext base N) left)
    (second : CInputRef (storageContext base N) right) :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (.product first second) =
      .product
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N first)
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N second) := by
  exact congrArg
    (fun read : CInputRef
        (Native.cellsContext (storageContext base N) (storage_empty base noQuantum N) N)
        (.product left right) =>
      read.underRetained
        (Native.cellsContext (storageContext base N)
          (storage_empty base noQuantum N) N).canonicalFreshKey
        (.bits (measurementBits N))
        (Native.cellsContext (storageContext base N)
          (storage_empty base noQuantum N) N).canonicalFreshKey_fresh)
    (MeasurementCells.liftInput_product 2
      (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N first)
      (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N second)
      (measurementBits N))

/-- The complete setup establishes the zero seed for the original quantum bank
for every input store and external reference. -/
theorem setup_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History)) :
    BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel
      ((setup base noQuantum N input).execute Reference state) := by
  apply BasisSeeded.seq
    (ShorStyle.Canonical.Sampler.Retained.circuit (model := model input) base N)
    ((Native.Batch.Slots.allocate (model := model input) (sourceContext base N) N).seq
      ((Declared.prepare (storageContext base N) (storage_empty base noQuantum N) N input).seq
        (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)))
  apply BasisSeeded.seq
    (Native.Batch.Slots.allocate (model := model input) (sourceContext base N) N)
    ((Declared.prepare (storageContext base N) (storage_empty base noQuantum N) N input).seq
      (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input))
  apply BasisSeeded.seq
    (Declared.prepare (storageContext base N) (storage_empty base noQuantum N) N input)
    (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)
  exact Declared.initial_seeded (storageContext base N)
    (storage_empty base noQuantum N) N input _

/-- The actual source sampler and all later allocations preserve the complete
uniform parameter/source mixture and every external-reference block. -/
theorem setup_source_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((setup base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          weight (parameterValue input value)
            (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
      leftRef rightRef := by
  let sampled := ShorStyle.Canonical.Sampler.Retained.circuit
    (model := model input) base N
  let storage := Native.Batch.Slots.allocate
    (model := model input) (sourceContext base N) N
  let initialized := (Declared.prepare (storageContext base N)
    (storage_empty base noQuantum N) N input).seq
      (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)
  let initialState := storage.execute Reference (sampled.execute Reference state)
  let oldParameter := Native.Batch.Slots.liftWrite N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
  let oldSource := Native.Batch.Slots.liftWrite N
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)
  let pair : CInputRef (storageContext base N)
      (.product (ParameterShape N) (.bits (residueSamplingBits N))) :=
    .product (.storage oldParameter.toCStorageRef) (.storage oldSource.toCStorageRef)
  let pairWeight := fun value : (CShape.product (ParameterShape N)
      (.bits (residueSamplingBits N))).Value => weight value.first value.second
  let observe := fun store : Store (context base noQuantum N) => weight
    (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
    (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
  have lifted := lifted_product base noQuantum N
    (.storage oldParameter.toCStorageRef) (.storage oldSource.toCStorageRef)
  have beforeBank := Circuit.referenceFiberSum_execute_seq
    (Declared.prepare (storageContext base N) (storage_empty base noQuantum N) N input)
    (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)
    initialState (fun store => pairWeight (store.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N pair)))
    leftRef rightRef
  have beforeSlots := Native.Batch.Slots.allocate_pair_reference
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model) (classicalOracles := .empty)
    (sourceContext base N) N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)
    (sampled.execute Reference state) weight leftRef rightRef
  have original := ShorStyle.Canonical.Sampler.Retained.samplerRetained_parameter_sample_reference
    (model := model input) input.samplerInput state weight leftRef rightRef
  have aligned := congrArg
    (fun read : CInputRef (context base noQuantum N)
        (.product (ParameterShape N) (.bits (residueSamplingBits N))) =>
      ExecutionState.referenceFiberSum (initialized.execute Reference initialState)
        (fun entry _ => pairWeight (entry.1.read read)) leftRef rightRef)
    (lifted.trans (congrArg₂ CInputRef.product
      (underBank_read base noQuantum N oldParameter)
      (underBank_read base noQuantum N oldSource)))
  exact (Circuit.referenceFiberSum_execute_seq sampled (storage.seq initialized)
    state observe leftRef rightRef).trans
      ((Circuit.referenceFiberSum_execute_seq storage initialized
        (sampled.execute Reference state) observe leftRef rightRef).trans
          (aligned.symm.trans (beforeBank.trans
            ((initialized_input_reference base noQuantum N input pair initialState pairWeight
              leftRef rightRef).trans (beforeSlots.trans original)))))

private theorem fixedInput_product {left right : CShape}
    (first : CInputRef (sourceContext base N) left)
    (second : CInputRef (sourceContext base N) right) :
    fixedInput base N (.product first second) =
      .product (fixedInput base N first) (fixedInput base N second) :=
  congrArg
    (fun read : CInputRef
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16)
        (.product left right) =>
      read.underRetained
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Native.Batch.Slots.samples (sourceContext base N)
          (measurementBits N) 16).canonicalFreshKey_fresh)
    (Native.Batch.Slots.slotsInput_product (measurementBits N) first second 16)

private theorem fixedInput_storage {shape : CShape}
    (ref : CWriteRef (sourceContext base N) shape) :
    fixedInput base N (.storage ref.toCStorageRef) =
      .storage (Native.Batch.Slots.liftWrite N ref).toCStorageRef :=
  congrArg
    (fun read : CInputRef
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16) shape =>
      read.underRetained
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Native.Batch.Slots.samples (sourceContext base N)
          (measurementBits N) 16).canonicalFreshKey_fresh)
    (Native.Batch.Slots.slotsInput_storage (measurementBits N) ref 16)

private theorem fixedInput_reference {shape : CShape}
    (observed : CInputRef (sourceContext base N) shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sourceContext base N) Reference ((model input).HiddenState × History))
    (weight : shape.Value → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Native.Batch.Slots.allocate (model := model input) (sourceContext base N) N).execute
        Reference state)
      (fun entry _ => weight (entry.1.read (fixedInput base N observed))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read observed)) left right := by
  let ctx := sourceContext base N
  let previous := Native.Batch.Slots.allocateSamples
    (model := model input) ctx (measurementBits N) 16
  let middle := Native.Batch.Slots.samples ctx (measurementBits N) 16
  let finalCell := Circuit.retain (model := model input) middle middle.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) middle.canonicalFreshKey_fresh
  exact (Circuit.referenceFiberSum_execute_seq previous finalCell state
    (fun store => weight (store.read (fixedInput base N observed))) left right).trans
      ((Circuit.referenceFiberSum_execute_retain_input
        (Native.Batch.Slots.slotsInput (measurementBits N) observed 16)
        middle.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
        middle.canonicalFreshKey_fresh (previous.execute Reference state)
        weight left right).trans
          (Native.Batch.Slots.allocateSamples_reference ctx (measurementBits N)
            observed 16 state weight left right))

/-- The actual setup draws its source jointly with every original caller read
and preserves each external-reference matrix coefficient. -/
theorem setup_input_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((setup base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (entry.1.read observed) (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
        left right := by
  let sampled := ShorStyle.Canonical.Sampler.Retained.circuit
    (model := model input) base N
  let storage := Native.Batch.Slots.allocate
    (model := model input) (sourceContext base N) N
  let initialized := (Declared.prepare (storageContext base N)
    (storage_empty base noQuantum N) N input).seq
      (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)
  let originalRead : CInputRef (sourceContext base N)
      (.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))) :=
    .product (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed)
      (.product
        (.storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef)
        (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef))
  let oldRead := fixedInput base N originalRead
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
  have lifted : Native.liftInput (storageContext base N)
      (storage_empty base noQuantum N) N oldRead = finalRead := by
    let oldCaller := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
    let oldParameter := ShorStyle.Canonical.Sampler.Retained.parameterRef base N
    let oldSource := ShorStyle.Canonical.Sampler.Retained.sampleRef base N
    have fixedPair := (fixedInput_product base N (.storage oldParameter.toCStorageRef)
      (.storage oldSource.toCStorageRef)).trans
        (congrArg₂ CInputRef.product (fixedInput_storage base N oldParameter)
          (fixedInput_storage base N oldSource))
    have fixedTriple := (fixedInput_product base N oldCaller
      (.product (.storage oldParameter.toCStorageRef)
        (.storage oldSource.toCStorageRef))).trans
          (congrArg (CInputRef.product (fixedInput base N oldCaller)) fixedPair)
    have firstLift := congrArg
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N) fixedTriple
    have secondLift := lifted_product base noQuantum N
      (fixedInput base N oldCaller)
      (.product (.storage (Native.Batch.Slots.liftWrite N oldParameter).toCStorageRef)
        (.storage (Native.Batch.Slots.liftWrite N oldSource).toCStorageRef))
    have pairLift := (lifted_product base noQuantum N
      (.storage (Native.Batch.Slots.liftWrite N oldParameter).toCStorageRef)
      (.storage (Native.Batch.Slots.liftWrite N oldSource).toCStorageRef)).trans
        (congrArg₂ CInputRef.product
          (underBank_read base noQuantum N (Native.Batch.Slots.liftWrite N oldParameter))
          (underBank_read base noQuantum N (Native.Batch.Slots.liftWrite N oldSource)))
    exact firstLift.trans (secondLift.trans
      (congrArg (CInputRef.product (callerInput base noQuantum N observed)) pairLift))
  have aligned := congrArg
    (fun read : CInputRef (context base noQuantum N)
        (.product shape (.product (ParameterShape N) (.bits (residueSamplingBits N)))) =>
      ExecutionState.referenceFiberSum (initialized.execute Reference initialState)
        (fun entry _ => readWeight (entry.1.read read)) left right) lifted
  have beforeBank := (Circuit.referenceFiberSum_execute_seq
    (Declared.prepare (storageContext base N) (storage_empty base noQuantum N) N input)
    (Declared.allocate (storageContext base N) (storage_empty base noQuantum N) N input)
    initialState (fun store => readWeight (store.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N oldRead)))
    left right).trans
      (initialized_input_reference base noQuantum N input oldRead initialState
        readWeight left right)
  have beforeSlots := fixedInput_reference base N input originalRead
    (sampled.execute Reference state) readWeight left right
  have original := ShorStyle.Canonical.Sampler.Retained.samplerRetained_reference_input
    (model := model input) input.samplerInput observed state weight left right
  exact (Circuit.referenceFiberSum_execute_seq sampled (storage.seq initialized)
    state observe left right).trans
      ((Circuit.referenceFiberSum_execute_seq storage initialized
        (sampled.execute Reference state) observe left right).trans
          (aligned.symm.trans (beforeBank.trans (beforeSlots.trans original))))

/-- The actual complete code has the sixteen-slot joint Born law conditioned on
the source and parameter produced by its physical setup. -/
theorem code_conditional_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((setup base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        ∏ index : Fin 16, Declared.sourceWeight N input
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)) leftRef rightRef := by
  exact (Circuit.referenceFiberSum_execute_seq
    (setup base noQuantum N input) (firstBatch base noQuantum N input) state
    (fun store => weight
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
      terminalIndicator base noQuantum N 16 id outcomes store)
    leftRef rightRef).trans
    (firstTerminals_reference base noQuantum N input _
      (setup_seeded base noQuantum N input state) weight outcomes leftRef rightRef)

/-- The complete physical sixteen-sample program combines the real uniform
source draw with its parameter-conditioned joint quantum Born law. -/
theorem code_joint_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input).execute Reference state)
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
              Declared.sourceWeight N input (parameterValue input value) (outcomes index)))
      leftRef rightRef := by
  exact (code_conditional_reference base noQuantum N input state weight outcomes
    leftRef rightRef).trans
    (setup_source_reference base noQuantum N input state
      (fun parameter source => weight parameter source *
        ∏ index : Fin 16, Declared.sourceWeight N input parameter (outcomes index))
      leftRef rightRef)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
