/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Outcome
import all QuantumAlg.Core.Measure.RealWeights
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Conditional source Born law for the actual declared Shor sample

The complete selected member, phase measurements and paid packing have the
source Born law in each original store-reference block.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma source_weight (amplitude coefficient : ℂ) :
    amplitude * coefficient * star amplitude = ((‖amplitude‖ ^ 2 : ℝ) : ℂ) * coefficient := by
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun value : ℂ => value * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

private lemma bits_indicator (width : Nat) (left right : Fin width → Bool) :
    (if CShape.Value.bits left = CShape.Value.bits right then (1 : ℂ) else 0) =
      if left = right then 1 else 0 := by
  by_cases same : left = right
  · subst right
    simp only
  · have different : CShape.Value.bits left ≠ CShape.Value.bits right :=
      fun equality => same (CShape.Value.bits.inj equality)
    simp only [if_neg different, if_neg same]


variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)
  (sameWires : base.quantumWires = (layout N).wires)

-- Measurement and packing transport the reference fiber through the actual stores.
private lemma measured_packed_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (observe : Store (Storage.context base N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
        (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
        (readouts base N sameWires)).seq
        (.classical (BitWord.application (packing base N)))).execute
          (environment input) Reference state)
      (fun entry _ => observe entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry basis => observe
          ((measuredStore base N sameWires entry.1 basis).applyOp
            (packing base N))) leftRef rightRef := by
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [packing_execute base N]
  simp only [ExecutionState.referenceFiberSum_mapClassical]
  exact Circuit.measurementSequence_referenceFiberSum (environment := environment input)
    (readouts base N sameWires) state _ leftRef rightRef

private lemma weighted_fiber {Basis : Type} [Fintype Basis]
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
lemma body_outcome_weighted_reference
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    (readWeight : Store (Storage.context base N) → ℂ)
    (readWeight_stable : ∀ store basis,
      readWeight ((measuredStore base N sameWires store basis).applyOp
        (packing base N)) = readWeight store)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds (Storage.context base N).quantumLayout.zeroLabel state)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base N sameWires parameter).execute (environment input) Reference state)
      (fun entry _ => readWeight entry.1 *
        (if entry.1.read (.storage (Storage.resultRef base N).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ∑ original : Store (Storage.context base N),
        (readWeight original *
          (((OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).outcomePMF
          (DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
            (selectedBase (original.read (Storage.liftInput base N parameter))))
          outcome).toReal : ℂ)) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
            ((Storage.context base N).quantumLayout.zeroLabel, rightRef) := by
  let observed := fun store : Store (Storage.context base N) =>
    readWeight store *
      (if store.read (.storage (Storage.resultRef base N).toCStorageRef) =
        CShape.Value.bits outcome then (1 : ℂ) else 0)
  have first := Circuit.referenceFiberSum_execute_seq
    (environment := environment input) (selected base N sameWires parameter)
    ((Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts base N sameWires)).seq
      (.classical (BitWord.application (packing base N)))) state observed
        leftRef rightRef
  refine first.trans ((measured_packed_reference base N input sameWires
    ((selected base N sameWires parameter).execute (environment input) Reference state)
    observed leftRef rightRef).trans ?_)
  let bornWeight := fun original : Store (Storage.context base N) =>
    fun basis : (Storage.context base N).register.Index =>
      readWeight original * (if (show Fin (phaseBits N) → Bool from
        (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).readout
          (basisEquiv N ((Storage.quantumWires base N).trans sameWires)
            basis)) = outcome
      then (1 : ℂ) else 0)
  have actualWeight (store : Store (Storage.context base N))
      (basis : (Storage.context base N).register.Index) :
      observed ((measuredStore base N sameWires store basis).applyOp
          (packing base N)) = bornWeight store basis := by
    have packed := packed_output base N sameWires store basis
    have indicator := congrArg
      (fun value : (CShape.bits (phaseBits N)).Value =>
        if value = CShape.Value.bits outcome then (1 : ℂ) else 0) packed
    have retained := readWeight_stable store basis
    dsimp only [observed, bornWeight]
    rw [retained]
    exact congrArg (fun value : ℂ => readWeight store * value)
      (indicator.trans (bits_indicator (phaseBits N) _ outcome))
  simp only [actualWeight]
  rw [BasisSeeded.fiber_store_blocks, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
            (selectedBase (original.read (Storage.liftInput base N parameter)))
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
      ((Storage.context base N).quantumLayout.zeroLabel, rightRef)
  have terms :
      (∑ basis : (Storage.context base N).register.Index, bornWeight original basis *
        (((selected base N sameWires parameter).execute
          (environment input) Reference state).filterClassical
          (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) =
      ∑ basis : (Storage.context base N).register.Index, bornWeight original basis *
        (((‖source.normalized
          (basisEquiv N ((Storage.quantumWires base N).trans sameWires)
            basis)‖ ^ 2 : ℝ) : ℂ) *
            coefficient) := by
    apply Finset.sum_congr rfl
    intro basis _
    exact congrArg (fun value : ℂ => bornWeight original basis * value)
      ((selected_seed_entry base N input sameWires parameter state seeded
        original basis basis leftRef rightRef).trans (source_weight _ _))
  have rearranged :
      (∑ basis : (Storage.context base N).register.Index,
        bornWeight original basis *
          (((‖source.normalized
            (basisEquiv N ((Storage.quantumWires base N).trans sameWires)
              basis)‖ ^ 2 : ℝ) : ℂ) * coefficient)) =
      ∑ basis : (Storage.context base N).register.Index,
        (if (show Fin (phaseBits N) → Bool from
          (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).readout
            (basisEquiv N ((Storage.quantumWires base N).trans sameWires)
              basis)) = outcome then (1 : ℂ) else 0) *
          (((‖source.normalized
            (basisEquiv N ((Storage.quantumWires base N).trans sameWires)
              basis)‖ ^ 2 : ℝ) : ℂ) * (readWeight original * coefficient)) := by
    apply Finset.sum_congr rfl
    intro basis _
    dsimp only [bornWeight]
    ring
  refine terms.trans (rearranged.trans
    ((weighted_fiber _ _ _ (readWeight original * coefficient)).trans ?_))
  have transported :=
    (basisEquiv N ((Storage.quantumWires base N).trans sameWires)).sum_comp
    (fun basis => if (show Fin (phaseBits N) → Bool from
      (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).readout basis) = outcome then
      ‖source.normalized basis‖ ^ 2 else 0)
  have born := transported.trans
    (TerminalZMeasure.outcomePMF_toReal
      (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)) source outcome).symm
  calc
    _ = (((OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).outcomePMF
      source outcome).toReal : ℂ) * (readWeight original * coefficient) :=
        congrArg (fun probability : ℝ =>
          (probability : ℂ) * (readWeight original * coefficient)) born
    _ = _ := by ring

/-- The ordinary conditional Born law is the unit-weight case. -/
lemma body_outcome_reference
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds (Storage.context base N).quantumLayout.zeroLabel state)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base N sameWires parameter).execute (environment input) Reference state)
      (fun entry _ => if entry.1.read (.storage (Storage.resultRef base N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store (Storage.context base N),
        (((OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).outcomePMF
          (DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
            (selectedBase (original.read (Storage.liftInput base N parameter))))
          outcome).toReal : ℂ) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
            ((Storage.context base N).quantumLayout.zeroLabel, rightRef) := by
  simpa only [one_mul] using
    (body_outcome_weighted_reference base N input sameWires parameter
      (fun _ => (1 : ℂ)) (by intro _ _; rfl) state seeded outcome leftRef rightRef)

/-- Two store observations agreeing after each actual measurement and pack
have identical reference fibers after the declared body. -/
lemma body_reference_congr
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    (left right : Store (Storage.context base N) → ℂ)
    (agree : ∀ store basis,
      left ((measuredStore base N sameWires store basis).applyOp
        (packing base N)) =
      right ((measuredStore base N sameWires store basis).applyOp
        (packing base N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((body base N sameWires parameter).execute (environment input) Reference state)
      (fun entry _ => left entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((body base N sameWires parameter).execute (environment input) Reference state)
      (fun entry _ => right entry.1) leftRef rightRef := by
  let previous := (selected base N sameWires parameter).execute (environment input) Reference state
  let tail := ((Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts base N sameWires)).seq
    (.classical (BitWord.application (packing base N))))
  have leftSeq := Circuit.referenceFiberSum_execute_seq (environment := environment input)
    (selected base N sameWires parameter) tail state left leftRef rightRef
  have rightSeq := Circuit.referenceFiberSum_execute_seq (environment := environment input)
    (selected base N sameWires parameter) tail state right leftRef rightRef
  have leftMeasured := measured_packed_reference base N input sameWires
    previous left leftRef rightRef
  have rightMeasured := measured_packed_reference base N input sameWires
    previous right leftRef rightRef
  calc
    _ = ExecutionState.referenceFiberSum previous
      (fun entry basis => left ((measuredStore base N sameWires entry.1 basis).applyOp
        (packing base N))) leftRef rightRef := leftSeq.trans leftMeasured
    _ = ExecutionState.referenceFiberSum previous
      (fun entry basis => right ((measuredStore base N sameWires entry.1 basis).applyOp
        (packing base N))) leftRef rightRef := by
          apply congrArg (fun observe =>
            ExecutionState.referenceFiberSum previous observe leftRef rightRef)
          funext entry basis
          exact agree entry.1 basis
    _ = _ := (rightSeq.trans rightMeasured).symm


end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
