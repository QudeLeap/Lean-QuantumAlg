/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.State
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Measure.RealWeights

/-!
# Conditional Simon Born observations on the actual retained bank

Actual finite measurement writes and paid packing produce the original
first-register outcome. Every earlier structural read outside the selected
sample slot stays in the same joint reference observation. The low-level seed
is supplied by the actual preparation or reset, never by an algorithm input.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem source_weight (amplitude coefficient : ℂ) :
    amplitude * coefficient * star amplitude = ((‖amplitude‖ ^ 2 : ℝ) : ℂ) * coefficient := by
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun value : ℂ => value * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

private theorem bits_indicator (width : Nat) (left right : Fin width → Bool) :
    (if CShape.Value.bits left = CShape.Value.bits right then (1 : ℂ) else 0) =
      if left = right then 1 else 0 := by
  by_cases same : left = right
  · subst right
    simp only
  · have different : CShape.Value.bits left ≠ CShape.Value.bits right :=
      fun equality => same (CShape.Value.bits.inj equality)
    simp only [if_neg different, if_neg same]


variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

private theorem readout_key (index : Fin n) :
    (readout base noQuantum n count index).output.key = (cells base noQuantum n count index).key :=
  FiniteReadout.transported_key
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) _)
    (cells base noQuantum n count index)

private theorem readout_value (index : Fin n)
    (store : Store (context base noQuantum n count)) :
    (store.read (.storage (readout base noQuantum n count index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum n count index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) _)
    (cells base noQuantum n count index) store

private theorem readouts_nodup :
    ((readouts base noQuantum n count).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum n count left).symm.trans
    (same.trans (readout_key base noQuantum n count right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

private theorem measured_cell (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) (index : Fin n) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum n count) store
      (Circuit.measurementBasisPath (readouts base noQuantum n count) basis)).read
        (.storage (cells base noQuantum n count index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum n count index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts base noQuantum n count)
    (readouts_nodup base noQuantum n count) (readout base noQuantum n count index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (context base noQuantum n count).register.Index)
    (index : Fin (2 * n)) :
    (basis (wireEquiv n (nativeSimon_context_wires base noQuantum n count) index)).val =
      ((SimonsProblem.layout n).binaryIndexEquiv.symm
        (basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (bankLayout n)
    (context base noQuantum n count).quantumLayout
    (layoutWires n (nativeSimon_context_wires base noQuantum n count))
  have value := Execution.basisOfEqualWires_value (bankLayout n)
    (context base noQuantum n count).quantumLayout
    (layoutWires n (nativeSimon_context_wires base noQuantum n count))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv n (nativeSimon_context_wires base noQuantum n count) index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (SimonsProblem.layout n).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (SimonsProblem.layout n).toQuantumLayout.Basis => (source index).val)
    inverse).symm

private theorem measured_bit (basis : (context base noQuantum n count).register.Index)
    (index : Fin n) :
    decide ((basis (readout base noQuantum n count index).wire).val = 1) =
      (SimonsProblem.measurement n).readout
        (basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis) index := by
  let source := (SimonsProblem.measurement n).logical_idx index
  let binary := basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis
  have finiteValue := wire_value base noQuantum n count basis source
  have bit := (SimonsProblem.layout n).binaryIndexEquiv_bit
    ((SimonsProblem.layout n).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv ((SimonsProblem.layout n).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit ((2 * n) - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- The actual writes and paid packing compute the original first-register outcome. -/
theorem nativeSimon_packed_output (index : Fin count)
    (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum n count) store
      (Circuit.measurementBasisPath (readouts base noQuantum n count) basis)).applyOp
        (packing base noQuantum n count index)).read
          (.storage (sampleRef base noQuantum n count index).toCStorageRef) =
      CShape.Value.bits ((SimonsProblem.measurement n).readout
        (basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis)) := by
  refine (Store.read_applyOp_output _ (packing base noQuantum n count index)).trans ?_
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts base noQuantum n count) store
      (Circuit.measurementBasisPath (readouts base noQuantum n count) basis)).read
        (.storage (cells base noQuantum n count index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measured_cell]
  exact measured_bit base noQuantum n count basis index


private theorem measured_packed_reference {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {input output : CShape}
    (pack : ClassicalOp input output ctx ctx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (observe : Store ctx → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((Circuit.measurementSequence readouts).seq (.classical pack)).execute Reference state)
      (fun entry _ => observe entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry basis => observe
        ((Circuit.writeMeasurementPath readouts entry.1
          (Circuit.measurementBasisPath readouts basis)).applyOp pack)) left right := by
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical,
    Circuit.execute_classical_mapClassical]
  exact Circuit.measurementSequence_referenceFiberSum readouts state _ left right

private theorem weighted_fiber {Basis : Type} [Fintype Basis]
    (predicate : Basis → Prop) (decision : DecidablePred predicate)
    (value : Basis → ℝ) (coefficient : ℂ) :
    (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
      ((value basis : ℂ) * coefficient)) =
      ((∑ basis : Basis,
        @ite ℝ (predicate basis) (decision basis) (value basis) 0 : ℝ) : ℂ) * coefficient := by
  have terms :
      (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
        ((value basis : ℂ) * coefficient)) =
      ∑ basis : Basis,
        ((@ite ℝ (predicate basis) (decision basis) (value basis) 0) : ℂ) * coefficient := by
    apply Finset.sum_congr rfl
    intro basis _
    by_cases selected : predicate basis
    · simp only [if_pos selected, one_mul]
    · simp only [if_neg selected, zero_mul, Complex.ofReal_zero]
  exact terms.trans ((Finset.sum_mul _ _ _).symm.trans
    (congrArg (fun total : ℂ => total * coefficient)
      (Complex.ofReal_sum (s := Finset.univ)
        (fun basis => @ite ℝ (predicate basis) (decision basis) (value basis) 0)).symm))

/-- Actual measurement and packing preserve an old structural read outside the selected slot. -/
theorem nativeSimon_packed_input (index : Fin count) {shape : CShape}
    (other : CInputRef (bankContext base noQuantum n count) shape)
    (separate : (bankSlot base noQuantum n count index).key ∉ other.storageKeys)
    (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum n count) store
      (Circuit.measurementBasisPath (readouts base noQuantum n count) basis)).applyOp
        (packing base noQuantum n count index)).read (MeasurementCells.liftInput 2 other n) =
      store.read (MeasurementCells.liftInput 2 other n) := by
  have packSeparate : (packing base noQuantum n count index).outputRef.key ∉
      (MeasurementCells.liftInput 2 other n).storageKeys := by
    change (MeasurementCells.liftWrite 2 (bankSlot base noQuantum n count index) n).key ∉ _
    rw [MeasurementCells.liftWrite_key, MeasurementCells.liftInput_storageKeys]
    exact separate
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (packing base noQuantum n count index)
    (MeasurementCells.liftInput 2 other n) packSeparate).trans ?_
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp present
  rw [readout_key]
  exact MeasurementCells.reference_not_mem_liftInput 2 other n position

private theorem unitary_seed_entry (sampling : SamplingCircuit n)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel state)
    (original : Store (context base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((Circuit.unitary (member n (nativeSimon_context_wires base noQuantum n count) sampling)
      (nativeSimon_member_physicalIdx n (nativeSimon_context_wires base noQuantum n count)
        sampling)).execute Reference state).filterClassical
          (fun entry => entry.1 = original)).quantumMarginal.matrix
            (left, leftRef) (right, rightRef) =
      sampling.evolvedState.normalized
        (basisEquiv n (nativeSimon_context_wires base noQuantum n count) left) *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        ((context base noQuantum n count).quantumLayout.zeroLabel, leftRef)
        ((context base noQuantum n count).quantumLayout.zeroLabel, rightRef) *
      star (sampling.evolvedState.normalized
        (basisEquiv n (nativeSimon_context_wires base noQuantum n count) right)) := by
  have filtered := Circuit.unitary_store_filter
    (member n (nativeSimon_context_wires base noQuantum n count) sampling)
    (nativeSimon_member_physicalIdx n (nativeSimon_context_wires base noQuantum n count) sampling)
    state (fun store => store = original)
  have entries := congrArg
    (fun density : DensityOperator
        (Register.prod (context base noQuantum n count).register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) filtered
  refine entries.trans ((BasisSeeded.unitary_entry _ state seeded
    (member n (nativeSimon_context_wires base noQuantum n count) sampling).matrix
    original left right leftRef rightRef).trans ?_)
  rw [nativeSimon_member_zero_amplitude, nativeSimon_member_zero_amplitude]
  rfl

/-- One actual sample factors its source Born probability from every earlier input-Ref weight. -/
theorem nativeSimon_sample_outcome_reference (sampling : SamplingCircuit n) (index : Fin count)
    {shape : CShape} (other : CInputRef (bankContext base noQuantum n count) shape)
    (separate : (bankSlot base noQuantum n count index).key ∉ other.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel state)
    (weight : shape.Value → ℂ) (outcome : Outcome n) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((sample base noQuantum n count sampling index).execute Reference state)
      (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)) *
        if entry.1.read (.storage (sampleRef base noQuantum n count index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ((sampling.outcomePMF outcome).toReal : ℂ) *
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)))
          leftRef rightRef := by
  let observed := fun store : Store (context base noQuantum n count) =>
    weight (store.read (MeasurementCells.liftInput 2 other n)) *
      if store.read (.storage (sampleRef base noQuantum n count index).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0
  let unitary := Circuit.unitary
    (member n (nativeSimon_context_wires base noQuantum n count) sampling)
    (nativeSimon_member_physicalIdx n (nativeSimon_context_wires base noQuantum n count) sampling)
  have first := Circuit.referenceFiberSum_execute_seq unitary
    ((Circuit.measurementSequence (readouts base noQuantum n count)).seq
      (.classical (packing base noQuantum n count index))) state observed leftRef rightRef
  refine first.trans ((measured_packed_reference (readouts base noQuantum n count)
    (packing base noQuantum n count index) (unitary.execute Reference state)
    observed leftRef rightRef).trans ?_)
  let indicator := fun basis : (context base noQuantum n count).register.Index =>
    if (SimonsProblem.measurement n).readout
      (basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis) = outcome
    then (1 : ℂ) else 0
  let oldWeight := fun store : Store (context base noQuantum n count) =>
    weight (store.read (MeasurementCells.liftInput 2 other n))
  have actualWeight (store : Store (context base noQuantum n count))
      (basis : (context base noQuantum n count).register.Index) :
      observed ((Circuit.writeMeasurementPath (readouts base noQuantum n count) store
        (Circuit.measurementBasisPath (readouts base noQuantum n count) basis)).applyOp
          (packing base noQuantum n count index)) = oldWeight store * indicator basis := by
    dsimp only [observed, oldWeight, indicator]
    rw [nativeSimon_packed_input base noQuantum n count index other separate,
      nativeSimon_packed_output]
    exact congrArg (fun value : ℂ =>
      weight (store.read (MeasurementCells.liftInput 2 other n)) * value)
      (bits_indicator n _ outcome)
  simp only [actualWeight]
  refine (BasisSeeded.fiber_store_blocks (unitary.execute Reference state)
    (fun store basis => oldWeight store * indicator basis) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  have stores :
      (∑ original : Store (context base noQuantum n count),
        ∑ basis : (context base noQuantum n count).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store (context base noQuantum n count),
        ((sampling.outcomePMF outcome).toReal : ℂ) *
          (oldWeight original *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
              ((context base noQuantum n count).quantumLayout.zeroLabel, leftRef)
              ((context base noQuantum n count).quantumLayout.zeroLabel, rightRef)) := by
    apply Finset.sum_congr rfl
    intro original _
    let coefficient := oldWeight original *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        ((context base noQuantum n count).quantumLayout.zeroLabel, leftRef)
        ((context base noQuantum n count).quantumLayout.zeroLabel, rightRef)
    have terms :
        (∑ basis : (context base noQuantum n count).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
        ∑ basis : (context base noQuantum n count).register.Index, indicator basis *
          (((‖sampling.evolvedState.normalized
            (basisEquiv n (nativeSimon_context_wires base noQuantum n count) basis)‖ ^ 2 : ℝ) : ℂ) *
              coefficient) := by
      apply Finset.sum_congr rfl
      intro basis _
      rw [unitary_seed_entry base noQuantum n count sampling state seeded,
        source_weight]
      dsimp only [coefficient]
      ring
    refine terms.trans ((weighted_fiber _ _ _ coefficient).trans ?_)
    apply congrArg (fun probability : ℝ => (probability : ℂ) * coefficient)
    exact ((basisEquiv n (nativeSimon_context_wires base noQuantum n count)).sum_comp
      (fun basis => if (SimonsProblem.measurement n).readout basis = outcome then
        ‖sampling.evolvedState.normalized basis‖ ^ 2 else 0)).trans
      (TerminalZMeasure.outcomePMF_toReal (SimonsProblem.measurement n)
        sampling.evolvedState outcome).symm
  refine stores.trans ?_
  rw [← Finset.mul_sum]
  exact congrArg (fun coefficient : ℂ => ((sampling.outcomePMF outcome).toReal : ℂ) * coefficient)
    (BasisSeeded.referenceFiberSum_seed _ state seeded oldWeight leftRef rightRef).symm

/-- A later actual reset-sample round has the same conditional law for arbitrary incoming states. -/
theorem nativeSimon_reusedSample_outcome_reference (sampling : SamplingCircuit n)
    (index : Fin count) {shape : CShape}
    (other : CInputRef (bankContext base noQuantum n count) shape)
    (separate : (bankSlot base noQuantum n count index).key ∉ other.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History)
    (weight : shape.Value → ℂ) (outcome : Outcome n) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reusedSample base noQuantum n count sampling index).execute Reference state)
      (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)) *
        if entry.1.read (.storage (sampleRef base noQuantum n count index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ((sampling.outcomePMF outcome).toReal : ℂ) *
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)))
          leftRef rightRef := by
  have first := Circuit.referenceFiberSum_execute_seq (reset base noQuantum n count)
    (sample base noQuantum n count sampling index) state
    (fun store => weight (store.read (MeasurementCells.liftInput 2 other n)) *
      if store.read (.storage (sampleRef base noQuantum n count index).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0) leftRef rightRef
  have born := nativeSimon_sample_outcome_reference base noQuantum n count sampling index
    other separate ((reset base noQuantum n count).execute Reference state)
    (nativeSimon_reset_seeded base noQuantum n count state) weight outcome leftRef rightRef
  have retained := nativeSimon_reset_reference base noQuantum n count state
    (fun store => weight (store.read (MeasurementCells.liftInput 2 other n))) leftRef rightRef
  exact first.trans (born.trans (congrArg
    (fun coefficient : ℂ => ((sampling.outcomePMF outcome).toReal : ℂ) * coefficient) retained))

end

end QuantumAlg.SimonsProblem.FixedSample.Native
