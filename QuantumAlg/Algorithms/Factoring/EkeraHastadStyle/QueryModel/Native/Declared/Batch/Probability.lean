/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Sample.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Sample.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Selected.Law

/-!
# Chronological joint Born law of the actual declared EH bank

Each stage resets the same physical bank, measures the original exponent
register and copies those finite cells into one of sixteen persistent slots.
The state and reference matrix remain explicit throughout the sequence.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The exact joint event reads the actual chronological sample cells. -/
def terminalIndicator (count : Nat) (indices : Fin count → Fin 16)
    (outcomes : Fin count → Fin (measurementBits N) → Bool)
    (store : Store (context base noQuantum N)) : ℂ :=
  ∏ index : Fin count,
    if store.read (.storage (terminalRef base noQuantum N (indices index)).toCStorageRef) =
      CShape.Value.bits (outcomes index) then 1 else 0

private def conditionalProduct (count : Nat)
    (outcomes : Fin count → Fin (measurementBits N) → Bool)
    (parameter : (ParameterShape N).Value) : ℂ :=
  ∏ index : Fin count, Declared.sourceWeight N input parameter (outcomes index)

private theorem conditionalProduct_step (count : Nat)
    (outcomes : Fin (count + 1) → Fin (measurementBits N) → Bool)
    (parameter : (ParameterShape N).Value) (weight : ℂ) :
    (weight * conditionalProduct N input count
      (fun index => outcomes index.succ) parameter) *
      Declared.sourceWeight N input parameter (outcomes 0) =
        weight * conditionalProduct N input (count + 1) outcomes parameter := by
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

private theorem range_reference :
    ∀ (count : Nat) (indices : Fin count → Fin 16) (_distinct : Function.Injective indices)
      {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
      (_measuredSeparate : ∀ position,
        (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
          observed.storageKeys)
      (_workingSeparate :
        (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
          observed.storageKeys)
      (_slotSeparate : ∀ index,
        (terminalRef base noQuantum N (indices index)).key ∉ observed.storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State (context base noQuantum N) Reference
        ((model input).HiddenState × History))
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
        (entry.1.read observed) * conditionalProduct N input count outcomes
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef)))
        leftRef rightRef := by
  intro count
  induction count with
  | zero =>
      intro indices _distinct shape observed _measuredSeparate _workingSeparate
        _slotSeparate Reference History _ state weight outcomes leftRef rightRef
      have executed := Circuit.execute_id_mapClassical
        (model := model input) Reference state
      have mapped := congrArg
        (fun output : State (context base noQuantum N) Reference
          ((model input).HiddenState × (History × Unit)) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight
              (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
              (entry.1.read observed)) leftRef rightRef) executed
      have transported := mapped.trans (ExecutionState.referenceFiberSum_mapClassical
        state (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
          _ leftRef rightRef)
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
          (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
            joint.storageKeys := by
        intro position present
        exact (List.mem_append.mp present).elim (measuredSeparate position)
          (terminal_measured_separate base noQuantum N position (indices 0))
      have tailWorking :
          (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
            joint.storageKeys := by
        intro present
        exact (List.mem_append.mp present).elim workingSeparate
          (terminal_working_separate base noQuantum N (indices 0))
      have tailSlots : ∀ index : Fin count,
          (terminalRef base noQuantum N (indices index.succ)).key ∉ joint.storageKeys := by
        intro index present
        rcases List.mem_append.mp present with original | headKey
        · exact slotSeparate index.succ original
        · have same := terminal_keys base noQuantum N
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
          conditionalProduct N input count (fun index => outcomes index.succ) old.first
      let parameterRead : CInputRef (context base noQuantum N) (ParameterShape N) :=
        .storage (parameterRef base noQuantum N).toCStorageRef
      have firstMeasured : ∀ position,
          (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
            (CInputRef.product parameterRead observed).storageKeys := by
        intro position present
        exact (List.mem_append.mp present).elim
          (parameter_measured_separate base noQuantum N position) (measuredSeparate position)
      have firstWorking :
          (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
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
      have firstLaw := reusedSample_joint_reference base noQuantum N input
        (indices 0) (.product parameterRead observed) firstMeasured firstWorking firstSlot
        state firstWeight (outcomes 0) leftRef rightRef
      have reordered := reference_congr base noQuantum N advanced
        (fun store => tailWeight (store.read parameterRead) (store.read joint) *
          conditionalProduct N input count (fun index => outcomes index.succ)
            (store.read parameterRead))
        (fun store => firstWeight (store.read (.product parameterRead observed)) *
          headIndicator (store.read (.storage head.toCStorageRef))) (fun store => by
        change (weight (store.read parameterRead) (store.read observed) *
          headIndicator (store.read (.storage head.toCStorageRef))) *
            conditionalProduct N input count _ (store.read parameterRead) =
          (weight (store.read parameterRead) (store.read observed) *
            conditionalProduct N input count _ (store.read parameterRead)) *
              headIndicator (store.read (.storage head.toCStorageRef))
        ring) leftRef rightRef
      have combined := reference_congr base noQuantum N state
        (fun store => firstWeight (store.read (.product parameterRead observed)) *
          Declared.sourceWeight N input
            (store.read (Native.liftInput (storageContext base N)
              (storage_empty base noQuantum N) N (parameter base N))) (outcomes 0))
        (fun store => weight (store.read parameterRead) (store.read observed) *
          conditionalProduct N input (count + 1) outcomes
            (store.read parameterRead)) (fun store => by
        have readEqual := congrArg store.read
          (parameter_read base noQuantum N)
        change (weight (store.read parameterRead) (store.read observed) *
          conditionalProduct N input count _ (store.read parameterRead)) * _ = _
        rw [readEqual]
        exact conditionalProduct_step N input count outcomes (store.read parameterRead)
          (weight (store.read parameterRead) (store.read observed))) leftRef rightRef
      exact (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef).trans (aligned.trans (tailLaw.trans
          (reordered.trans (firstLaw.trans combined))))

/-- Sixteen paid same-bank stages retain any separated old read jointly with
their physical outcomes and their one actual retained parameter. -/
theorem reusedTerminals_frame_reference
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotsSeparate : ∀ index, (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : (ParameterShape N).Value → shape.Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Circuit.forRange 16 (reusedSample base noQuantum N input)).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read observed) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read observed) *
        ∏ index : Fin 16, Declared.sourceWeight N input
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)) leftRef rightRef := by
  simpa only [conditionalProduct, id_eq] using
    (range_reference base noQuantum N input 16 id Function.injective_id observed
      measuredSeparate workingSeparate slotsSeparate state weight outcomes leftRef rightRef)

/-- The original source read is a specialization of the paid reuse frame law. -/
theorem reusedTerminals_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
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
        ∏ index : Fin 16, Declared.sourceWeight N input
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)) leftRef rightRef :=
  reusedTerminals_frame_reference base noQuantum N input
    (.storage (sourceRef base noQuantum N).toCStorageRef)
    (source_measured_separate base noQuantum N)
    (source_working_separate base noQuantum N)
    (fun index member => terminal_source_ne base noQuantum N index
      (List.mem_singleton.mp member))
    state weight outcomes leftRef rightRef


/-- The first prepared member and fifteen paid successors retain any
protected structural read jointly with all sixteen physical outcomes. -/
theorem firstTerminals_frame_reference
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : ∀ index, (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference ((model input).HiddenState × History))
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
        ∏ index : Fin 16, Declared.sourceWeight N input
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)) leftRef rightRef := by
  let count := 15
  let indices : Fin 16 → Fin 16 := id
  have distinct : Function.Injective indices := Function.injective_id
  let head := terminalRef base noQuantum N (indices 0)
  let joint : CInputRef (context base noQuantum N)
      (.product shape (.bits (measurementBits N))) :=
    .product observed (.storage head.toCStorageRef)
  let first := (Declared.body (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).seq (copy base noQuantum N input (indices 0))
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
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        joint.storageKeys := by
    intro position present
    exact (List.mem_append.mp present).elim (measuredSeparate position)
      (terminal_measured_separate base noQuantum N position (indices 0))
  have tailWorking :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        joint.storageKeys := by
    intro present
    exact (List.mem_append.mp present).elim workingSeparate
      (terminal_working_separate base noQuantum N (indices 0))
  have tailSlots : ∀ index : Fin count,
      (terminalRef base noQuantum N (indices index.succ)).key ∉ joint.storageKeys := by
    intro index present
    rcases List.mem_append.mp present with original | headKey
    · exact slotSeparate index.succ original
    · have same := terminal_keys base noQuantum N
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
      conditionalProduct N input count (fun index => outcomes index.succ) old.first
  let parameterRead : CInputRef (context base noQuantum N) (ParameterShape N) :=
    .storage (parameterRef base noQuantum N).toCStorageRef
  have firstMeasured : ∀ position,
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        (CInputRef.product parameterRead observed).storageKeys := by
    intro position present
    exact (List.mem_append.mp present).elim
      (parameter_measured_separate base noQuantum N position) (measuredSeparate position)
  have firstWorking :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
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
  have firstLaw := body_copy_joint_reference base noQuantum N input
    (indices 0) (.product parameterRead observed) firstMeasured firstWorking firstSlot
    state seeded firstWeight (outcomes 0) leftRef rightRef
  have reordered := reference_congr base noQuantum N advanced
    (fun store => tailWeight (store.read parameterRead) (store.read joint) *
      conditionalProduct N input count (fun index => outcomes index.succ)
        (store.read parameterRead))
    (fun store => firstWeight (store.read (.product parameterRead observed)) *
      headIndicator (store.read (.storage head.toCStorageRef))) (fun store => by
    change (weight (store.read parameterRead) (store.read observed) *
      headIndicator (store.read (.storage head.toCStorageRef))) *
        conditionalProduct N input count _ (store.read parameterRead) =
      (weight (store.read parameterRead) (store.read observed) *
        conditionalProduct N input count _ (store.read parameterRead)) *
          headIndicator (store.read (.storage head.toCStorageRef))
    ring) leftRef rightRef
  have firstFiber := (BasisSeeded.referenceFiberSum_seed
    (context base noQuantum N).quantumLayout.zeroLabel state seeded
    (fun store => firstWeight (store.read (.product parameterRead observed)) *
      Declared.sourceWeight N input
        (store.read (Native.liftInput (storageContext base N)
          (storage_empty base noQuantum N) N (parameter base N))) (outcomes 0))
    leftRef rightRef).symm
  have combined := reference_congr base noQuantum N state
    (fun store => firstWeight (store.read (.product parameterRead observed)) *
      Declared.sourceWeight N input
        (store.read (Native.liftInput (storageContext base N)
          (storage_empty base noQuantum N) N (parameter base N))) (outcomes 0))
    (fun store => weight (store.read parameterRead) (store.read observed) *
      conditionalProduct N input (count + 1) outcomes (store.read parameterRead)) (fun store => by
    have readEqual := congrArg store.read
      (parameter_read base noQuantum N)
    change (weight (store.read parameterRead) (store.read observed) *
      conditionalProduct N input count _ (store.read parameterRead)) * _ = _
    rw [readEqual]
    exact conditionalProduct_step N input count outcomes (store.read parameterRead)
      (weight (store.read parameterRead) (store.read observed))) leftRef rightRef
  exact (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
    leftRef rightRef).trans (aligned.trans (tailLaw.trans
      (reordered.trans (firstLaw.trans (firstFiber.trans combined)))))

/-- The original source read is a specialization of the protected-read law. -/
theorem firstTerminals_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference ((model input).HiddenState × History))
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
        ∏ index : Fin 16, Declared.sourceWeight N input
          (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (outcomes index)) leftRef rightRef :=
  firstTerminals_frame_reference base noQuantum N input
    (.storage (sourceRef base noQuantum N).toCStorageRef)
    (source_measured_separate base noQuantum N)
    (source_working_separate base noQuantum N)
    (fun index member => terminal_source_ne base noQuantum N index
      (List.mem_singleton.mp member))
    state seeded weight outcomes leftRef rightRef


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
