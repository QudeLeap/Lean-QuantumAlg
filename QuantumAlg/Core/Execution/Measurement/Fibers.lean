/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Measure.Instrument

/-!
# Actual measured classical fibers with every reference matrix entry

The finite sum below observes the diagonal local-system coordinates while
keeping arbitrary, possibly distinct, external-reference coordinates. It is
a scalar observation of the existing state's matrix, not an execution state
or measurement object. Actual classical writes transport the observation,
and the existing Z interpreter supplies its actual outcomes and path.

The resulting formula describes each observed classical result jointly with
the full reference operator, including its off-diagonal entries
[dW19, qcnotes.tex:5409,5420,6827]. It assumes neither a pure input nor an
independent reference, and it includes the empty measurement sequence.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

variable {C : Type} [Fintype C] {R Reference : Register}

/-- A finite local-system diagonal sum retaining one complete reference matrix entry. -/
def referenceFiberSum (state : ExecutionState C (Register.prod R Reference))
    (weight : C → R.Index → ℂ) (left right : Reference.Index) : ℂ :=
  ∑ basis : R.Index, ∑ value : C,
    weight value basis * (state.block value).matrix (basis, left) (basis, right)

/-- A real classical pushforward transports the weight and keeps both reference coordinates. -/
theorem referenceFiberSum_mapClassical {D : Type} [Fintype D] [DecidableEq D]
    (state : ExecutionState C (Register.prod R Reference)) (update : C → D)
    (weight : D → R.Index → ℂ) (left right : Reference.Index) :
    referenceFiberSum (state.mapClassical update) weight left right =
      referenceFiberSum state (fun value basis => weight (update value) basis) left right := by
  unfold referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  change (∑ output : D, weight output basis *
    (∑ value : C, if update value = output then (state.block value).matrix else 0)
      (basis, left) (basis, right)) = _
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- A local Z read supplies its actual value on both local diagonal coordinates. -/
theorem referenceFiberSum_measureZ {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]
    (state : ExecutionState C (Register.prod R Reference)) (readout : R.Index → Outcome)
    (weight : (C × Outcome) → R.Index → ℂ) (left right : Reference.Index) :
    referenceFiberSum (state.measureZ (fun basis => readout basis.1)) weight left right =
      referenceFiberSum state (fun value basis => weight (value, readout basis) basis)
        left right := by
  unfold referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Fintype.sum_prod_type, measureZ_block, ZMeasurement.branch_matrix, and_self,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The full reference entry of an observed classical block is its exact local fiber. -/
theorem mapClassical_block_referenceFiberSum {D : Type} [Fintype D] [DecidableEq D]
    (state : ExecutionState C (Register.prod R Reference)) (read : C → D) (value : D)
    (left right : Reference.Index) :
    (∑ basis : R.Index,
      ((state.mapClassical read).block value).matrix (basis, left) (basis, right)) =
      referenceFiberSum state (fun source _ => if read source = value then 1 else 0)
        left right := by
  change (∑ basis : R.Index,
    (∑ source : C, if read source = value then (state.block source).matrix else 0)
      (basis, left) (basis, right)) = _
  simp only [referenceFiberSum, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    ite_mul, one_mul, zero_mul]

end ExecutionState

namespace Circuit

open Execution

/-- Actual ordered writes and path values determine each complete reference observation. -/
theorem measurementSequence_referenceFiberSum {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (weight : (Store ctx × (History × (measurementSequence readouts).Path)) →
      ctx.register.Index → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((measurementSequence readouts).execute Reference state)
      weight left right =
      ExecutionState.referenceFiberSum state (fun value basis =>
        weight (writeMeasurementPath readouts value.1 (measurementBasisPath readouts basis),
          (value.2, measurementBasisPath readouts basis)) basis) left right := by
  induction readouts generalizing History with
  | nil =>
      simp only [measurementSequence, execute_id, State.skip, State.mapHistory,
        ExecutionState.referenceFiberSum_mapClassical, writeMeasurementPath, measurementBasisPath]
  | cons head tail induction =>
      change ExecutionState.referenceFiberSum
        ((Circuit.seq (.measureZ head.wire head.output)
          (measurementSequence tail)).execute Reference state) weight left right = _
      rw [execute_seq]
      simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
      rw [induction, execute_measureZ]
      simp only [State.measureZ, ExecutionState.referenceFiberSum_mapClassical]
      exact ExecutionState.referenceFiberSum_measureZ
        (R := ctx.register) (Reference := Reference) state
        (fun basis : ctx.register.Index => basis head.wire)
        (fun value basis => weight
          (writeMeasurementPath tail (value.1.1.write head.output (.finite value.2))
            (measurementBasisPath tail basis),
            (value.1.2, (value.2, measurementBasisPath tail basis))) basis)
        left right

/-- The actual observed result retains exactly its original complete reference fiber. -/
theorem measurementSequence_observed_reference_entry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {History D : Type}
    [Fintype History] [Fintype D] (state : State ctx Reference History)
    (read : Store ctx × (History × (measurementSequence readouts).Path) → D) (value : D)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      DensityOperator.matrix
        ((((measurementSequence readouts).execute Reference state).mapClassical read).block value)
        (basis, left) (basis, right)) =
      ExecutionState.referenceFiberSum state (fun original basis =>
        if read (writeMeasurementPath readouts original.1 (measurementBasisPath readouts basis),
          (original.2, measurementBasisPath readouts basis)) = value then 1 else 0) left right := by
  rw [ExecutionState.mapClassical_block_referenceFiberSum, measurementSequence_referenceFiberSum]

end Circuit

end

end QuantumAlg
