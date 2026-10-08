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
# Actual measured Store values and their exact Born fibers

A diagonal sum is a finite linear observation of the same execution state's
matrix entries. It is not a second runtime state or a prescribed outcome
probability. The lemmas below propagate this observation through actual
classical writes and the existing sequential measurement interpreter.

The final formula sums the initial diagonal entries whose actual writes and
recorded paths produce the observed value. It includes every unmeasured
system and external-reference coordinate, following the projective Born rule
[dW19, qcnotes.tex:5409,5420]. No normalization or positive-width premise is
needed, and overwriting a classical cell retains its actual sequential meaning.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

variable {C : Type} [Fintype C] {R : Register}

/-- A finite linear observation of the actual classical and quantum diagonal entries. -/
def diagonalSum (state : ExecutionState C R) (weight : C → R.Index → ℂ) : ℂ :=
  ∑ basis : R.Index, ∑ value : C, weight value basis * (state.block value).matrix basis basis

/-- A real classical pushforward moves only the value argument of a diagonal observation. -/
theorem diagonalSum_mapClassical {D : Type} [Fintype D] [DecidableEq D]
    (state : ExecutionState C R) (update : C → D)
    (weight : D → R.Index → ℂ) :
    diagonalSum (state.mapClassical update) weight =
      diagonalSum state (fun value basis => weight (update value) basis) := by
  unfold diagonalSum
  apply Finset.sum_congr rfl
  intro basis _
  change (∑ output : D, weight output basis *
    (∑ value : C, if update value = output then (state.block value).matrix else 0) basis basis) = _
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- On each diagonal entry, the actual measurement outcome equals its readout value. -/
theorem diagonalSum_measureZ {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]
    (state : ExecutionState C R) (readout : R.Index → Outcome)
    (weight : (C × Outcome) → R.Index → ℂ) :
    diagonalSum (state.measureZ readout) weight =
      diagonalSum state (fun value basis => weight (value, readout basis) basis) := by
  unfold diagonalSum
  apply Finset.sum_congr rfl
  intro basis _
  simp only [Fintype.sum_prod_type, measureZ_block, ZMeasurement.branch_matrix, and_self,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- An observed classical block's mass is exactly its diagonal fiber sum. -/
theorem mapClassical_block_mass_diagonalSum {D : Type} [Fintype D] [DecidableEq D]
    (state : ExecutionState C R)
    (read : C → D) (value : D) :
    ((state.mapClassical read).block value).mass =
      (diagonalSum state (fun source _ => if read source = value then 1 else 0)).re := by
  change (∑ basis : R.Index,
    (∑ source : C, if read source = value then (state.block source).matrix else 0)
      basis basis).re = _
  congr 1
  simp only [diagonalSum, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    ite_mul, one_mul, zero_mul]

end ExecutionState

namespace Circuit

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

open Execution

/-- The diagonal observation follows the actual sequential Store writes and actual path values. -/
theorem measurementSequence_diagonalSum {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (services.HiddenState × H))
    (weight : (Store ctx × (services.HiddenState × (H ×
      (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      readouts).Path))) →
      (Register.prod ctx.register Reference).Index → ℂ) :
    ExecutionState.diagonalSum ((measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      readouts).execute Reference state) weight =
      ExecutionState.diagonalSum state (fun value basis =>
        weight (writeMeasurementPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts value.1
          (measurementBasisPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts basis.1),
          (value.2.1, (value.2.2, measurementBasisPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts basis.1)))
            basis) := by
  induction readouts generalizing H with
  | nil =>
      simp only [measurementSequence, execute_id,
        ExecutionState.diagonalSum_mapClassical,
        writeMeasurementPath,
        measurementBasisPath]
      rfl
  | cons head tail ih =>
      change ExecutionState.diagonalSum
        ((Circuit.seq (.measureZ head.wire head.output)
          (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) tail)).execute Reference
            state) weight = _
      rw [execute_seq]
      simp only [State.mapHistory, ExecutionState.diagonalSum_mapClassical]
      rw [ih, execute_measureZ]
      simp only [ExecutionState.diagonalSum_mapClassical,
        ExecutionState.diagonalSum_measureZ]
      rfl

/-- The mass of an actual measured observation is its initial-state Born fiber,
with the final Store and recorded path computed by the real ordered writes. -/
theorem measurementSequence_observed_mass {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {H D : Type}
    [Fintype H] [Fintype D] (state : State ctx Reference (services.HiddenState × H))
    (read : Store ctx × (services.HiddenState × (H ×
      (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      readouts).Path)) → D) (value : D) :
    ((((measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts).execute Reference
      state).mapClassical read).block
      value).mass =
      (ExecutionState.diagonalSum state (fun original basis =>
        if read (writeMeasurementPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts original.1
          (measurementBasisPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts basis.1),
          (original.2.1, (original.2.2, measurementBasisPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) readouts
            basis.1))) = value then 1 else 0)).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum, measurementSequence_diagonalSum]

end Circuit

end

end QuantumAlg
