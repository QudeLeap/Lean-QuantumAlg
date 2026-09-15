/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Semantics
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Encoding
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Measure.RealWeights
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation

/-!
# The actual original-width sample and its source Born law

The actual finite-cell writes and charged pack produce the original ordered
exponent outcome. Its conditional law is the original source Born PMF, with
the entire input-store reference operator as coefficient. Faithful encoding
independence then identifies that law with the already accepted prepared
sample distribution, without identifying their different resource ledgers.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original-width XOR member has the already accepted source exponent law. -/
theorem nativeOracle_outcomePMF_eq_selected {N : Nat} (input : Input N)
    (parameter : (ParameterShape N).Value) :
    (ShortDLP.measurement (parameters N)).outcomePMF
      (ShortDLP.BornProbability.evolvedState (encoding input)
        (parameterUnit parameter) (parameterTarget parameter)) = selectedOutcomePMF parameter := by
  let : NeZero N := ⟨Nat.ne_of_gt input.modulus_pos⟩
  unfold selectedOutcomePMF
  rw [ShortDLP.CompiledMAU.outcomePMF_eq_ideal _ _ _ _ _ _ input.modulus_gt_one
    ((modulus_lt_arithmeticCapacity N))]
  apply PMF.ext
  intro outcome
  obtain ⟨label, rfl⟩ :=
    (ShortDLP.BornProbability.shortDLPMeasurementOutcome_bijective
      (parameters N)).surjective outcome
  obtain ⟨pair, rfl⟩ := prodEquiv.surjective label
  have independent := pairBornProbability_encoding_independent (shortLogBits N) (tradeoffBits N)
    (encoding input)
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
      (modulus_lt_arithmeticCapacity N)) (parameterUnit parameter) (parameterTarget parameter) pair
  exact (ShortDLP.BornProbability.shortDLPBornOutcomeProbability_eq_pairBornProbability
    (encoding input) (parameterUnit parameter) (parameterTarget parameter) pair).trans
    (independent.trans
      (ShortDLP.BornProbability.shortDLPBornOutcomeProbability_eq_pairBornProbability
        (params := ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
        (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
          (modulus_lt_arithmeticCapacity N))
        (parameterUnit parameter) (parameterTarget parameter) pair).symm)


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


variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem readout_key (index : Fin (measurementBits N)) :
    (readout base noQuantum N index).output.key = (cells base noQuantum N index).key :=
  FiniteReadout.transported_key
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N) _)
    (cells base noQuantum N index)

private theorem readout_value (index : Fin (measurementBits N))
    (store : Store (context base noQuantum N)) :
    (store.read (.storage (readout base noQuantum N index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum N index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N) _)
    (cells base noQuantum N index) store

private theorem readouts_nodup :
    ((readouts base noQuantum N).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum N left).symm.trans
    (same.trans (readout_key base noQuantum N right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

private theorem measured_cell (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) (index : Fin (measurementBits N)) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum N) store
      (Circuit.measurementBasisPath (readouts base noQuantum N) basis)).read
        (.storage (cells base noQuantum N index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum N index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts base noQuantum N)
    (readouts_nodup base noQuantum N) (readout base noQuantum N index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (context base noQuantum N).register.Index)
    (index : Fin (ShortDLP.totalQubits (parameters N))) :
    (basis (wireEquiv N (nativeOracle_context_wires base noQuantum N) index)).val =
      ((ShortDLP.layout (parameters N)).binaryIndexEquiv.symm
        (basisEquiv N (nativeOracle_context_wires base noQuantum N) basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (layout N)
    (context base noQuantum N).quantumLayout
    (layoutWires N (nativeOracle_context_wires base noQuantum N))
  have value := Execution.basisOfEqualWires_value (layout N)
    (context base noQuantum N).quantumLayout
    (layoutWires N (nativeOracle_context_wires base noQuantum N))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv N (nativeOracle_context_wires base noQuantum N) index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (ShortDLP.layout (parameters N)).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (ShortDLP.layout (parameters N)).toQuantumLayout.Basis => (source index).val)
    inverse).symm

private theorem measured_bit (basis : (context base noQuantum N).register.Index)
    (index : Fin (measurementBits N)) :
    decide ((basis (readout base noQuantum N index).wire).val = 1) =
      (ShortDLP.measurement (parameters N)).readout
        (basisEquiv N (nativeOracle_context_wires base noQuantum N) basis) index := by
  let source := (ShortDLP.measurement (parameters N)).logical_idx index
  let binary := basisEquiv N (nativeOracle_context_wires base noQuantum N) basis
  have finiteValue := wire_value base noQuantum N basis source
  have bit := (ShortDLP.layout (parameters N)).binaryIndexEquiv_bit
    ((ShortDLP.layout (parameters N)).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv ((ShortDLP.layout (parameters N)).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (ShortDLP.totalQubits (parameters N) - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- The same actual writes and final packing compute precisely the original exponent outcome. -/
theorem nativeOracle_packed_output (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum N) store
      (Circuit.measurementBasisPath (readouts base noQuantum N) basis)).applyOp
        (packing base noQuantum N)).read (.storage (resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits ((ShortDLP.measurement (parameters N)).readout
        (basisEquiv N (nativeOracle_context_wires base noQuantum N) basis)) := by
  refine (Store.read_applyOp_output _ (packing base noQuantum N)).trans ?_
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts base noQuantum N) store
      (Circuit.measurementBasisPath (readouts base noQuantum N) basis)).read
        (.storage (cells base noQuantum N index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measured_cell]
  exact measured_bit base noQuantum N basis index


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

/-- The actual selected, measured and packed outcome has the original conditional Born law. -/
theorem nativeOracle_body_outcome_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (outcome : Fin (measurementBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read (.storage (resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store (context base noQuantum N),
        ((selectedOutcomePMF (original.read (liftInput base noQuantum N parameter))
          outcome).toReal : ℂ) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  let observed := fun store : Store (context base noQuantum N) =>
    if store.read (.storage (resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then (1 : ℂ) else 0
  have first := Circuit.referenceFiberSum_execute_seq (selected base noQuantum N input parameter)
    ((Circuit.measurementSequence (readouts base noQuantum N)).seq
      (.classical (packing base noQuantum N))) state observed
        leftRef rightRef
  refine first.trans ((measured_packed_reference (readouts base noQuantum N)
    (packing base noQuantum N)
    ((selected base noQuantum N input parameter).execute Reference state)
    observed leftRef rightRef).trans ?_)
  let weight := fun _store : Store (context base noQuantum N) =>
    fun basis : (context base noQuantum N).register.Index =>
      if (show Fin (measurementBits N) → Bool from
        (ShortDLP.measurement (parameters N)).readout
          (basisEquiv N (nativeOracle_context_wires base noQuantum N) basis)) = outcome
      then (1 : ℂ) else 0
  have actualWeight (store : Store (context base noQuantum N))
      (basis : (context base noQuantum N).register.Index) :
      observed ((Circuit.writeMeasurementPath (readouts base noQuantum N) store
        (Circuit.measurementBasisPath (readouts base noQuantum N) basis)).applyOp
          (packing base noQuantum N)) = weight store basis := by
    have packed := nativeOracle_packed_output base noQuantum N store basis
    have indicator := congrArg
      (fun value : (CShape.bits (measurementBits N)).Value =>
        if value = CShape.Value.bits outcome then (1 : ℂ) else 0) packed
    exact indicator.trans (bits_indicator (measurementBits N) _ outcome)
  simp only [actualWeight]
  rw [BasisSeeded.fiber_store_blocks, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := ShortDLP.BornProbability.evolvedState (encoding input)
    (parameterUnit (original.read (liftInput base noQuantum N parameter)))
    (parameterTarget (original.read (liftInput base noQuantum N parameter)))
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
      ((context base noQuantum N).quantumLayout.zeroLabel, rightRef)
  have terms :
      (∑ basis : (context base noQuantum N).register.Index, weight original basis *
        (((selected base noQuantum N input parameter).execute Reference state).filterClassical
          (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) =
      ∑ basis : (context base noQuantum N).register.Index, weight original basis *
        (((‖source.normalized
          (basisEquiv N (nativeOracle_context_wires base noQuantum N) basis)‖ ^ 2 : ℝ) : ℂ) *
            coefficient) := by
    apply Finset.sum_congr rfl
    intro basis _
    exact congrArg (fun value : ℂ => weight original basis * value)
      ((nativeOracle_selected_seed_entry base noQuantum N input parameter state seeded
        original basis basis leftRef rightRef).trans (source_weight _ _))
  refine terms.trans ((weighted_fiber _ _ _ coefficient).trans ?_)
  apply congrArg (fun probability : ℝ => (probability : ℂ) * coefficient)
  have transported := (basisEquiv N (nativeOracle_context_wires base noQuantum N)).sum_comp
    (fun basis => if (show Fin (measurementBits N) → Bool from
      (ShortDLP.measurement (parameters N)).readout basis) = outcome then
      ‖source.normalized basis‖ ^ 2 else 0)
  exact transported.trans
    ((TerminalZMeasure.outcomePMF_toReal (ShortDLP.measurement (parameters N)) source outcome).symm
      |>.trans (congrArg (fun distribution => (distribution outcome).toReal)
        (nativeOracle_outcomePMF_eq_selected input
          (original.read (liftInput base noQuantum N parameter)))))


/-- The complete actual preparation prefix supplies its seed internally before the source law. -/
private theorem initialized_outcome_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    let initialized := (allocate base noQuantum N).execute Reference
      ((prepare base noQuantum N).execute Reference state)
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read (.storage (resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store (context base noQuantum N),
        ((selectedOutcomePMF (original.read (liftInput base noQuantum N parameter))
          outcome).toReal : ℂ) *
          (initialized.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  let observed := fun store : Store (context base noQuantum N) =>
    if store.read (.storage (resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then (1 : ℂ) else 0
  exact (Circuit.referenceFiberSum_execute_seq (prepare base noQuantum N)
    ((allocate base noQuantum N).seq (body base noQuantum N input parameter))
      state observed leftRef rightRef).trans
    ((Circuit.referenceFiberSum_execute_seq (allocate base noQuantum N)
      (body base noQuantum N input parameter)
      ((prepare base noQuantum N).execute Reference state) observed leftRef rightRef).trans
      (nativeOracle_body_outcome_reference base noQuantum N input parameter _
        (nativeOracle_initial_seeded base noQuantum N state) outcome leftRef rightRef))


private theorem initialized_reference_input (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : (ParameterShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((allocate base noQuantum N).execute Reference
        ((prepare base noQuantum N).execute Reference state))
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum N parameter)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read parameter))
        leftRef rightRef := by
  let prepared := (prepare base noQuantum N).execute Reference state
  let prior := MeasurementCells.liftInput 2 (bankInput base noQuantum N parameter)
    (measurementBits N)
  let retention := Circuit.retain (cellsContext base noQuantum N)
    (cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (cellsContext base noQuantum N).canonicalFreshKey_fresh
  have split := Circuit.referenceFiberSum_execute_seq
    (MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)) retention
    prepared (fun store => weight (store.read (liftInput base noQuantum N parameter)))
    leftRef rightRef
  have retained := Circuit.referenceFiberSum_execute_retain_input prior
    (cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (cellsContext base noQuantum N).canonicalFreshKey_fresh
    ((MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)).execute
      Reference prepared) weight leftRef rightRef
  have cellsPreserved := MeasurementCells.allocate_referenceFiberSum_input
    (bankInput base noQuantum N parameter) 2 (measurementBits N) prepared weight leftRef rightRef
  have preparationPreserved := Circuit.referenceFiberSum_execute_prepare_input parameter
    base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N) (preparation N) state weight leftRef rightRef
  exact split.trans (retained.trans (cellsPreserved.trans preparationPreserved))

/-- Actual outcomes have the original conditional law on the original stored parameter and Ref. -/
theorem nativeOracle_code_outcome_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read (.storage (resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ((selectedOutcomePMF (entry.1.read parameter) outcome).toReal : ℂ))
        leftRef rightRef := by
  let initialized := (allocate base noQuantum N).execute Reference
    ((prepare base noQuantum N).execute Reference state)
  let weight := fun value : (ParameterShape N).Value =>
    ((selectedOutcomePMF value outcome).toReal : ℂ)
  exact (initialized_outcome_reference base noQuantum N input parameter state outcome
    leftRef rightRef).trans
    ((BasisSeeded.referenceFiberSum_seed _ initialized
      (nativeOracle_initial_seeded base noQuantum N state)
      (fun store => weight (store.read (liftInput base noQuantum N parameter)))
      leftRef rightRef).symm.trans
        (initialized_reference_input base noQuantum N parameter state weight leftRef rightRef))

/-- The declared output PMF traces those same source weights on the complete original input. -/
theorem nativeOracle_outputDistribution (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) {Reference : Register}
    (original : Execution.Input base Reference) (outcome : Fin (measurementBits N) → Bool) :
    (run base noQuantum N input parameter).outputDistribution original (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun store _ => ((selectedOutcomePMF (store.read parameter) outcome).toReal : ℂ))
            reference reference).re := by
  let actual := run base noQuantum N input parameter
  let read := fun record : actual.Record => actual.result record
  have mapped := congrArg (fun probability : PMF (CShape.Value (.bits (measurementBits N))) =>
    probability (.bits outcome)) (ExecutionState.toPMF_mapClassical
      (actual.execute Reference original.state) (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply, ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro reference _
  exact (nativeOracle_code_outcome_reference base noQuantum N input parameter
    (original.state.mapClassical (fun store => (store, store))) outcome reference reference).trans
      (ExecutionState.referenceFiberSum_mapClassical original.state
        (fun store => (store, store)) _ reference reference)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
