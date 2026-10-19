/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Storage
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Execution.Laws
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Components.Classical.Model.BitWord.Placement

/-!
# Measured-output probability fibers of the actual native sampler

The selected-model interpreter writes physical Z outcomes to distinct cells,
then packs those same values. For any incoming state, including arbitrary
classical and external-reference correlations, each output block has exactly
the corresponding initial quantum-diagonal mass.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private lemma packedRead (t width : Nat)
    (store : Store (post ctx noQuantum t width)) :
    (store.applyOp (packing ctx noQuantum t width)).read
      (.storage (resultRef ctx noQuantum t width).toCStorageRef) =
      (packing ctx noQuantum t width).eval
        (store.read (MeasurementCells.input (resultContext ctx noQuantum t width) 2 t)) :=
  Store.read_applyOp_output store (packing ctx noQuantum t width)

private lemma selectedPackedRead (t width : Nat)
    (store : Store (post ctx noQuantum t width)) :
    (store.write (BitWord.application (packing ctx noQuantum t width)).output
      ((packing ctx noQuantum t width).eval
        (store.read (BitWord.application (packing ctx noQuantum t width)).input))).read
      (.storage (resultRef ctx noQuantum t width).toCStorageRef) =
      (packing ctx noQuantum t width).eval
        (store.read (MeasurementCells.input (resultContext ctx noQuantum t width) 2 t)) := by
  change (store.applyOp (packing ctx noQuantum t width)).read
    (.storage (resultRef ctx noQuantum t width).toCStorageRef) = _
  exact packedRead ctx noQuantum t width store

/-- Actual Z writes and packing preserve exactly the source Born fiber mass. -/
lemma readoutCode_block_mass {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post ctx noQuantum t width) Reference
      ((model t width).HiddenState × H))
    (output : CShape.Value (.bits t)) :
    ((((readoutCode ctx noQuantum t width).execute (Sampling.Native.environment access) Reference
      state).mapClassical
      (fun value => value.1.read
        (.storage (resultRef ctx noQuantum t width).toCStorageRef))).block output).mass =
      (∑ basis : (post ctx noQuantum t width).register.Index,
        if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout
          (outputBasisEquiv ctx noQuantum t width basis)) = output
          then state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.execute_classical_mapClassical
    (model := model t width) (environment := Sampling.Native.environment access)
    (BitWord.application (packing ctx noQuantum t width))
    (packing ctx noQuantum t width).eval
    (BitWord.bitWord_application_evaluate (packing ctx noQuantum t width)) Reference]
  simp only [ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.measurementSequence_diagonalSum]
  simp only [selectedPackedRead, packing_measured_value]
  calc
    _ = ∑ basis : (post ctx noQuantum t width).register.Index,
        (if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout
          (outputBasisEquiv ctx noQuantum t width basis)) = output
          then (1 : ℂ) else 0) * state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout
          (outputBasisEquiv ctx noQuantum t width basis)) = output
          then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro basis _
      split <;> simp only [one_mul, zero_mul]

private lemma pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

/-- The selected sampler's final output mass is the source coherent Born fiber. -/
lemma code_block_mass {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference ((model t width).HiddenState × H))
    (normalized : state.IsNormalized) (output : CShape.Value (.bits t)) :
    ((((code ctx noQuantum t width).execute (Sampling.Native.environment access) Reference
      state).mapClassical
      (fun value => value.1.read
        (.storage (resultRef ctx noQuantum t width).toCStorageRef))).block output).mass =
      ∑ basis : Fin (2 ^ (t + width)),
        if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout basis) = output
          then ‖OrderFinding.Native.evolvedVector access basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post ctx noQuantum t width).register.Index,
        if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout
          (outputBasisEquiv ctx noQuantum t width basis)) = output
          then
          ((beforeMeasurement ctx noQuantum t width).execute (Sampling.Native.environment access)
            Reference state).quantumMarginal.marginalLeft.matrix
            basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def] using
          readoutCode_block_mass ctx noQuantum access
            ((beforeMeasurement ctx noQuantum t width).execute (Sampling.Native.environment
              access) Reference state) output
    _ = (∑ basis : Fin (2 ^ (t + width)),
        if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout basis) = output
          then (DensityOperator.ofPure (OrderFinding.Native.evolvedVector access)).matrix
            basis basis else 0).re := by
      rw [beforeMeasurement_localDensity ctx noQuantum access state normalized]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (outputBasisEquiv ctx noQuantum t width).sum_comp
        (fun basis : Fin (2 ^ (t + width)) =>
          if CShape.Value.bits ((OrderFinding.Native.measurement t width).readout basis) = output
            then (DensityOperator.ofPure (OrderFinding.Native.evolvedVector access)).matrix
              basis basis else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted :
          CShape.Value.bits ((OrderFinding.Native.measurement t width).readout basis) = output
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
