/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse.Semantics

/-!
# Joint observations through one actual fixed-context sample

The actual measurement and both paid packs preserve structural reads outside
those destinations. Keeping any complex weight on such a read gives the
original conditional Born law with the entire reference operator. The reused
sample obtains its zero support from the actual reset. Neither statement
assumes independent outcomes, pure reference states or initial sample slots.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Slots.samples

private theorem classical_reference {ctx : RuntimeCtx .quantum} {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((Circuit.classical op).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.applyOp op)) leftRef rightRef := by
  simp only [Circuit.execute_classical_mapClassical,
    ExecutionState.referenceFiberSum_mapClassical]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem copy_reference (index : Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : Store (context base noQuantum N) → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((copy base noQuantum N index).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (copyStep base noQuantum N index entry.1).1) leftRef rightRef :=
  classical_reference _ state weight leftRef rightRef

private theorem copiedValue_packing (store : Store (context base noQuantum N)) :
    copiedValue base noQuantum N
      (store.applyOp (packing (storageContext base N) (storage_empty base noQuantum N) N)) =
      copiedValue base noQuantum N store := by
  apply congrArg (CShape.packFiniteBits (measurementBits N))
  apply Store.read_applyOp_of_not_mem_storageKeys
  exact CInputRef.fresh_not_mem_storageKeys_underRetained
    (.fixedVector fun index => .storage
      (MeasurementCells.reference
        (bankContext (storageContext base N) (storage_empty base noQuantum N) N)
        2 (measurementBits N) index).toCStorageRef)
    _ _ _

private theorem copiedValue_measured (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) :
    copiedValue base noQuantum N
      (Circuit.writeMeasurementPath
        (readouts (storageContext base N) (storage_empty base noQuantum N) N) store
        (Circuit.measurementBasisPath
          (readouts (storageContext base N) (storage_empty base noQuantum N) N) basis)) =
      CShape.Value.bits ((ShortDLP.measurement (parameters N)).readout
        (basisEquiv N (nativeOracle_context_wires
          (storageContext base N) (storage_empty base noQuantum N) N) basis)) := by
  apply congrArg CShape.Value.bits
  funext index
  let measured := Circuit.writeMeasurementPath
    (readouts (storageContext base N) (storage_empty base noQuantum N) N) store
    (Circuit.measurementBasisPath
      (readouts (storageContext base N) (storage_empty base noQuantum N) N) basis)
  change decide ((measured.read (.storage
    (cells (storageContext base N) (storage_empty base noQuantum N) N
      index).toCStorageRef)).toFin.val = 1) = _
  exact (congrArg (fun value : Nat => decide (value = 1))
    (measured_cell (storageContext base N) (storage_empty base noQuantum N) N
      store basis index)).trans
    (measured_bit (storageContext base N) (storage_empty base noQuantum N) N basis index)


private theorem measured_packed_read {shape : CShape}
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ index,
      (cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
        observed.storageKeys)
    (workingSeparate :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) :
    ((Circuit.writeMeasurementPath
      (readouts (storageContext base N) (storage_empty base noQuantum N) N) store
      (Circuit.measurementBasisPath
        (readouts (storageContext base N) (storage_empty base noQuantum N) N) basis)).applyOp
          (packing (storageContext base N) (storage_empty base noQuantum N) N)).read observed =
      store.read observed := by
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (packing (storageContext base N) (storage_empty base noQuantum N) N)
    observed workingSeparate).trans ?_
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rw [readout_key]
  exact measuredSeparate index

private theorem copied_measurement_observation {shape : CShape} (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) :
    let measured := (Circuit.writeMeasurementPath
      (readouts (storageContext base N) (storage_empty base noQuantum N) N) store
      (Circuit.measurementBasisPath
        (readouts (storageContext base N) (storage_empty base noQuantum N) N) basis)).applyOp
          (packing (storageContext base N) (storage_empty base noQuantum N) N)
    let copied := (copyStep base noQuantum N index measured).1
    weight (copied.read observed) *
      (if copied.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) =
    weight (store.read observed) *
      (if (show Fin (measurementBits N) → Bool from
        (ShortDLP.measurement (parameters N)).readout
        (basisEquiv N (nativeOracle_context_wires
          (storageContext base N) (storage_empty base noQuantum N) N) basis)) = outcome
        then 1 else 0) := by
  dsimp only
  erw [nativeOracle_batch_copy_frame base noQuantum N index observed slotSeparate,
    measured_packed_read base noQuantum N observed measuredSeparate workingSeparate,
    nativeOracle_batch_copy_read, copiedValue_packing, copiedValue_measured]
  exact congrArg (fun scalar : ℂ => weight (store.read observed) * scalar)
    (bits_indicator (measurementBits N) _ outcome)

private theorem body_copy_reference {shape : CShape} (input : Input N) (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((body (storageContext base N) (storage_empty base noQuantum N) N input
        (parameter base N)).seq (copy base noQuantum N index)).execute Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ∑ original : Store (context base noQuantum N),
        (weight (original.read observed) *
          ((selectedOutcomePMF (original.read
            (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
              (parameter base N))) outcome).toReal : ℂ)) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  classical
  let finish := fun store : Store (context base noQuantum N) =>
    weight (store.read observed) *
      (if store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0)
  let afterCopy := fun store : Store (context base noQuantum N) =>
    finish (copyStep base noQuantum N index store).1
  have copied := Circuit.referenceFiberSum_execute_seq
    (body (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    (copy base noQuantum N index) state finish leftRef rightRef
  have copyObserved := copy_reference base noQuantum N index
    ((body (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).execute Reference state) finish leftRef rightRef
  refine copied.trans (copyObserved.trans ?_)
  have first := Circuit.referenceFiberSum_execute_seq
    (selected (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    ((Circuit.measurementSequence
      (readouts (storageContext base N) (storage_empty base noQuantum N) N)).seq
        (.classical (packing (storageContext base N) (storage_empty base noQuantum N) N)))
    state afterCopy leftRef rightRef
  refine first.trans ((measured_packed_reference
    (readouts (storageContext base N) (storage_empty base noQuantum N) N)
    (packing (storageContext base N) (storage_empty base noQuantum N) N)
    ((selected (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).execute Reference state) afterCopy leftRef rightRef).trans ?_)
  have actualWeight := copied_measurement_observation base noQuantum N index observed
    measuredSeparate workingSeparate slotSeparate weight outcome
  let bornWeight := fun original : Store (context base noQuantum N) =>
    fun basis : (context base noQuantum N).register.Index => weight (original.read observed) *
      (if (show Fin (measurementBits N) → Bool from
        (ShortDLP.measurement (parameters N)).readout
          (basisEquiv N (nativeOracle_context_wires
            (storageContext base N) (storage_empty base noQuantum N) N) basis)) = outcome
        then (1 : ℂ) else 0)
  have replaced := congrArg
    (fun read : (Store (context base noQuantum N) ×
        (History × (selected (storageContext base N) (storage_empty base noQuantum N) N
          input (parameter base N)).Path)) →
          (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum
        ((selected (storageContext base N) (storage_empty base noQuantum N) N input
          (parameter base N)).execute Reference state) read leftRef rightRef)
    (funext fun entry => funext fun basis => actualWeight entry.1 basis)
  refine replaced.trans ((BasisSeeded.fiber_store_blocks
    ((selected (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).execute Reference state) bornWeight leftRef rightRef).trans ?_)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := ShortDLP.BornProbability.evolvedState (encoding input)
    (parameterUnit (original.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        (parameter base N))))
    (parameterTarget (original.read
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        (parameter base N))))
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
      ((context base noQuantum N).quantumLayout.zeroLabel, rightRef)
  have entries (basis : (context base noQuantum N).register.Index) :=
    (nativeOracle_selected_seed_entry (storageContext base N) (storage_empty base noQuantum N) N
      input (parameter base N) state seeded original basis basis leftRef rightRef).trans
      (source_weight _ _)
  have terms :
      (∑ basis : (context base noQuantum N).register.Index, bornWeight original basis *
        (((selected (storageContext base N) (storage_empty base noQuantum N) N input
          (parameter base N)).execute Reference state).filterClassical
            (fun entry => entry.1 = original)).quantumMarginal.matrix
              (basis, leftRef) (basis, rightRef)) =
      ∑ basis : (context base noQuantum N).register.Index, bornWeight original basis *
        (((‖source.normalized (basisEquiv N (nativeOracle_context_wires
          (storageContext base N) (storage_empty base noQuantum N) N) basis)‖ ^ 2 : ℝ) : ℂ) *
          coefficient) := by
    apply Finset.sum_congr rfl
    intro basis _
    exact congrArg (fun scalar : ℂ => bornWeight original basis * scalar) (entries basis)
  refine terms.trans ?_
  dsimp only [bornWeight]
  simp only [mul_assoc, ← Finset.mul_sum]
  apply congrArg (fun scalar : ℂ => weight (original.read observed) * scalar)
  refine (weighted_fiber _ _ _ coefficient).trans ?_
  apply congrArg (fun scalar : ℝ => (scalar : ℂ) * coefficient)
  have transported := (basisEquiv N (nativeOracle_context_wires
    (storageContext base N) (storage_empty base noQuantum N) N)).sum_comp
    (fun basis => if (show Fin (measurementBits N) → Bool from
      (ShortDLP.measurement (parameters N)).readout basis) = outcome then
      ‖source.normalized basis‖ ^ 2 else 0)
  exact transported.trans
    ((TerminalZMeasure.outcomePMF_toReal (ShortDLP.measurement (parameters N)) source outcome).symm
      |>.trans (congrArg (fun distribution => (distribution outcome).toReal)
        (nativeOracle_outcomePMF_eq_selected input
          (original.read (Native.liftInput (storageContext base N)
            (storage_empty base noQuantum N) N (parameter base N))))))

/-- A prepared actual member preserves a separated old read jointly with its new slot value. -/
theorem nativeOracle_batch_firstSample_reference {shape : CShape}
    (input : Input N) (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((body (storageContext base N) (storage_empty base noQuantum N) N input
        (parameter base N)).seq (copy base noQuantum N index)).execute Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read observed) *
        ((selectedOutcomePMF (entry.1.read
          (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
            (parameter base N))) outcome).toReal : ℂ)) leftRef rightRef :=
  (body_copy_reference base noQuantum N input index observed measuredSeparate workingSeparate
    slotSeparate state seeded weight outcome leftRef rightRef).trans
    (BasisSeeded.referenceFiberSum_seed _ state seeded _ leftRef rightRef).symm

/-- Paid reset establishes the same joint law for arbitrary old bank, slots, history and Ref. -/
theorem nativeOracle_batch_reusedSample_reference {shape : CShape}
    (input : Input N) (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position,
      (cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reusedSample base noQuantum N input index).execute Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read observed) *
        ((selectedOutcomePMF (entry.1.read
          (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
            (parameter base N))) outcome).toReal : ℂ)) leftRef rightRef := by
  let finish := fun store : Store (context base noQuantum N) =>
    weight (store.read observed) *
      (if store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0)
  have copied := Circuit.referenceFiberSum_execute_seq
    (reuse (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    (copy base noQuantum N index) state finish leftRef rightRef
  have copyObserved := copy_reference base noQuantum N index
    ((reuse (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).execute Reference state) finish leftRef rightRef
  have reset := Circuit.referenceFiberSum_execute_seq
    (resetBank (storageContext base N) (storage_empty base noQuantum N) N)
    (body (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    state (fun store => finish (copyStep base noQuantum N index store).1) leftRef rightRef
  have packed := Circuit.referenceFiberSum_execute_seq
    (body (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    (copy base noQuantum N index)
    ((resetBank (storageContext base N) (storage_empty base noQuantum N) N).execute Reference state)
    finish leftRef rightRef
  have packedCopy := copy_reference base noQuantum N index
    ((body (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).execute Reference
        ((resetBank (storageContext base N) (storage_empty base noQuantum N) N).execute
          Reference state)) finish leftRef rightRef
  have firstLaw := nativeOracle_batch_firstSample_reference base noQuantum N input index observed
    measuredSeparate workingSeparate slotSeparate _
    (nativeOracle_resetBank_seeded (storageContext base N) (storage_empty base noQuantum N) N
      state) weight outcome leftRef rightRef
  have resetLaw := nativeOracle_resetBank_reference
    (storageContext base N) (storage_empty base noQuantum N) N state
    (fun store => weight (store.read observed) *
      ((selectedOutcomePMF (store.read
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
          (parameter base N))) outcome).toReal : ℂ)) leftRef rightRef
  exact copied.trans (copyObserved.trans (reset.trans
    ((packed.trans packedCopy).symm.trans (firstLaw.trans resetLaw))))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
