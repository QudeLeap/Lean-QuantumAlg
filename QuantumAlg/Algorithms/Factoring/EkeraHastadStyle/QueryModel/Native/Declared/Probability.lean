/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Outcome
import all QuantumAlg.Core.Measure.RealWeights
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Conditional source Born law for the actual declared EH sample

The complete selected member, exponent measurements and paid packing have the
source Born law in each original store-reference block.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

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


variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

-- Measurement and packing transport the reference fiber through the actual stores.
private theorem measured_packed_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (observe : Store (Native.context base noQuantum N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((Circuit.measurementSequence (gates := AlgorithmGate.model)
        (oracles := ShortDLP.declaredModel (Native.encoding input))
        (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
        (readouts base noQuantum N)).seq
        (.classical (BitWord.application (packing base noQuantum N)))).execute Reference state)
      (fun entry _ => observe entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry basis => observe
          ((measuredStore base noQuantum N input entry.1 basis).applyOp
            (packing base noQuantum N))) leftRef rightRef := by
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [packing_execute]
  simp only [ExecutionState.referenceFiberSum_mapClassical]
  exact Circuit.measurementSequence_referenceFiberSum
    (readouts base noQuantum N) state _ leftRef rightRef

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

/-- The actual selected, measured and packed outcome has its conditional Born law
jointly with any classical weight preserved by measurement and packing. -/
theorem body_outcome_weighted_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (readWeight : Store (Native.context base noQuantum N) → ℂ)
    (readWeight_stable : ∀ store basis,
      readWeight ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)) = readWeight store)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (seeded : BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel state)
    (outcome : Fin (measurementBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base noQuantum N input parameter).execute Reference state)
      (fun entry _ => readWeight entry.1 *
        (if entry.1.read (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ∑ original : Store (Native.context base noQuantum N),
        (readWeight original * (((ShortDLP.measurement (Native.parameters N)).outcomePMF
          (ShortDLP.BornProbability.evolvedState (Native.encoding input)
            (parameterUnit (original.read (Native.liftInput base noQuantum N parameter)))
            (parameterTarget (original.read (Native.liftInput base noQuantum N parameter))))
          outcome).toReal : ℂ)) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  let observed := fun store : Store (Native.context base noQuantum N) =>
    readWeight store *
      (if store.read (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0)
  have first := Circuit.referenceFiberSum_execute_seq (selected base noQuantum N input parameter)
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts base noQuantum N)).seq
      (.classical (BitWord.application (packing base noQuantum N)))) state observed
        leftRef rightRef
  refine first.trans ((measured_packed_reference base noQuantum N input
    ((selected base noQuantum N input parameter).execute Reference state)
    observed leftRef rightRef).trans ?_)
  let bornWeight := fun original : Store (Native.context base noQuantum N) =>
    fun basis : (Native.context base noQuantum N).register.Index =>
      readWeight original * (if (show Fin (measurementBits N) → Bool from
        (ShortDLP.measurement (Native.parameters N)).readout
          (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)
            basis)) = outcome
      then (1 : ℂ) else 0)
  have actualWeight (store : Store (Native.context base noQuantum N))
      (basis : (Native.context base noQuantum N).register.Index) :
      observed ((measuredStore base noQuantum N input store basis).applyOp
          (packing base noQuantum N)) = bornWeight store basis := by
    have packed := packed_output base noQuantum N input store basis
    have indicator := congrArg
      (fun value : (CShape.bits (measurementBits N)).Value =>
        if value = CShape.Value.bits outcome then (1 : ℂ) else 0) packed
    have retained := readWeight_stable store basis
    dsimp only [observed, bornWeight]
    rw [retained]
    exact congrArg (fun value : ℂ => readWeight store * value)
      (indicator.trans (bits_indicator (measurementBits N) _ outcome))
  simp only [actualWeight]
  rw [BasisSeeded.fiber_store_blocks, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := ShortDLP.BornProbability.evolvedState (Native.encoding input)
    (parameterUnit (original.read (Native.liftInput base noQuantum N parameter)))
    (parameterTarget (original.read (Native.liftInput base noQuantum N parameter)))
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((Native.context base noQuantum N).quantumLayout.zeroLabel, leftRef)
      ((Native.context base noQuantum N).quantumLayout.zeroLabel, rightRef)
  have terms :
      (∑ basis : (Native.context base noQuantum N).register.Index, bornWeight original basis *
        (((selected base noQuantum N input parameter).execute Reference state).filterClassical
          (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) =
      ∑ basis : (Native.context base noQuantum N).register.Index, bornWeight original basis *
        (((‖source.normalized
          (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)
            basis)‖ ^ 2 : ℝ) : ℂ) *
            coefficient) := by
    apply Finset.sum_congr rfl
    intro basis _
    exact congrArg (fun value : ℂ => bornWeight original basis * value)
      ((selected_seed_entry base noQuantum N input parameter state seeded
        original basis basis leftRef rightRef).trans (source_weight _ _))
  have rearranged :
      (∑ basis : (Native.context base noQuantum N).register.Index,
        bornWeight original basis *
          (((‖source.normalized
            (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)
              basis)‖ ^ 2 : ℝ) : ℂ) * coefficient)) =
      ∑ basis : (Native.context base noQuantum N).register.Index,
        (if (show Fin (measurementBits N) → Bool from
          (ShortDLP.measurement (Native.parameters N)).readout
            (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)
              basis)) = outcome then (1 : ℂ) else 0) *
          (((‖source.normalized
            (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)
              basis)‖ ^ 2 : ℝ) : ℂ) * (readWeight original * coefficient)) := by
    apply Finset.sum_congr rfl
    intro basis _
    dsimp only [bornWeight]
    ring
  refine terms.trans (rearranged.trans
    ((weighted_fiber _ _ _ (readWeight original * coefficient)).trans ?_))
  have transported :=
    (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N)).sum_comp
    (fun basis => if (show Fin (measurementBits N) → Bool from
      (ShortDLP.measurement (Native.parameters N)).readout basis) = outcome then
      ‖source.normalized basis‖ ^ 2 else 0)
  have born := transported.trans
    (TerminalZMeasure.outcomePMF_toReal
      (ShortDLP.measurement (Native.parameters N)) source outcome).symm
  calc
    _ = (((ShortDLP.measurement (Native.parameters N)).outcomePMF
      source outcome).toReal : ℂ) * (readWeight original * coefficient) :=
        congrArg (fun probability : ℝ =>
          (probability : ℂ) * (readWeight original * coefficient)) born
    _ = _ := by ring

/-- The ordinary conditional Born law is the unit-weight case. -/
theorem body_outcome_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (seeded : BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel state)
    (outcome : Fin (measurementBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store (Native.context base noQuantum N),
        (((ShortDLP.measurement (Native.parameters N)).outcomePMF
          (ShortDLP.BornProbability.evolvedState (Native.encoding input)
            (parameterUnit (original.read (Native.liftInput base noQuantum N parameter)))
            (parameterTarget (original.read (Native.liftInput base noQuantum N parameter))))
          outcome).toReal : ℂ) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  simpa only [one_mul] using
    (body_outcome_weighted_reference base noQuantum N input parameter
      (fun _ => (1 : ℂ)) (by intro _ _; rfl) state seeded outcome leftRef rightRef)

/-- Two store observations agreeing after each actual measurement and pack
have identical reference fibers after the declared body. -/
theorem body_reference_congr (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (left right : Store (Native.context base noQuantum N) → ℂ)
    (agree : ∀ store basis,
      left ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)) =
      right ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base noQuantum N input parameter).execute Reference state)
      (fun entry _ => left entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((body base noQuantum N input parameter).execute Reference state)
      (fun entry _ => right entry.1) leftRef rightRef := by
  let previous := (selected base noQuantum N input parameter).execute Reference state
  let tail := ((Circuit.measurementSequence (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts base noQuantum N)).seq
    (.classical (BitWord.application (packing base noQuantum N))))
  have leftSeq := Circuit.referenceFiberSum_execute_seq
    (selected base noQuantum N input parameter) tail state left leftRef rightRef
  have rightSeq := Circuit.referenceFiberSum_execute_seq
    (selected base noQuantum N input parameter) tail state right leftRef rightRef
  have leftMeasured := measured_packed_reference base noQuantum N input
    previous left leftRef rightRef
  have rightMeasured := measured_packed_reference base noQuantum N input
    previous right leftRef rightRef
  calc
    _ = ExecutionState.referenceFiberSum previous
      (fun entry basis => left ((measuredStore base noQuantum N input entry.1 basis).applyOp
        (packing base noQuantum N))) leftRef rightRef := leftSeq.trans leftMeasured
    _ = ExecutionState.referenceFiberSum previous
      (fun entry basis => right ((measuredStore base noQuantum N input entry.1 basis).applyOp
        (packing base noQuantum N))) leftRef rightRef := by
          apply congrArg (fun observe =>
            ExecutionState.referenceFiberSum previous observe leftRef rightRef)
          funext entry basis
          exact agree entry.1 basis
    _ = _ := (rightSeq.trans rightMeasured).symm


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
