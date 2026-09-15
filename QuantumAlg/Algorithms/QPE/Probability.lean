/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Storage.Laws
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Execution.Laws
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Measure.Distribution

/-!
# The Born fibers of the actual phase-estimation output

The retained phase bits are read from the actual Z writes and closed packing
instruction. Summation over the same interpreter's histories, unmeasured
source coordinates, and external reference yields the original coherent
source-state Born fiber. No outcome distribution is an execution input.

-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

private theorem packedRead (t n : Nat) (store : Store (post t n)) :
    (store.applyOp (packing t n)).read (.storage (resultRef t n).toCStorageRef) =
      (packing t n).eval (store.read (MeasurementCells.input (resultContext t n) 2 t)) :=
  Store.read_applyOp_output store (packing t n)

/-- The actual measured and packed output has precisely the corresponding initial diagonal fiber. -/
theorem readoutCode_block_mass (t n : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (post t n) Reference H) (output : CShape.Value (.bits t)) :
    ((((readoutCode t n).execute Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef t n).toCStorageRef))).block output).mass =
      (∑ basis : (post t n).register.Index,
        if CShape.Value.bits ((qpeMeasurement t n).readout (outputBasisEquiv t n basis)) = output
          then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.execute_classical]
  simp only [State.classicalStep, ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.measurementSequence_diagonalSum]
  simp only [packedRead, packing_measured_value]
  calc
    _ = ∑ basis : (post t n).register.Index,
        (if CShape.Value.bits ((qpeMeasurement t n).readout (outputBasisEquiv t n basis)) = output
          then (1 : ℂ) else 0) * state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if CShape.Value.bits ((qpeMeasurement t n).readout (outputBasisEquiv t n basis)) = output
          then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro basis _
      split <;> simp only [one_mul, zero_mul]

private theorem pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

/-- Every final output-block mass is the original query-readout Born fiber,
derived from actual preparation, gates, measurements, storage writes and packing. -/
theorem code_block_mass {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference H)
    (promised : inputPromise P t state.quantumMarginal.marginalLeft)
    (output : CShape.Value (.bits t)) :
    ((((code P t).execute Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef t n).toCStorageRef))).block output).mass =
      ∑ basis : Fin (2 ^ (t + n)),
        if CShape.Value.bits ((qpeMeasurement t n).readout basis) = output then
          ‖(qpeEvolvedState P t).normalized basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post t n).register.Index,
        if CShape.Value.bits ((qpeMeasurement t n).readout (outputBasisEquiv t n basis)) = output
          then
          ((beforeMeasurement P t).execute Reference state).quantumMarginal.marginalLeft.matrix
            basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def] using
          readoutCode_block_mass t n ((beforeMeasurement P t).execute Reference state) output
    _ = (∑ basis : Fin (2 ^ (t + n)),
        if CShape.Value.bits ((qpeMeasurement t n).readout basis) = output then
          (DensityOperator.ofPure ((qpeEvolvedState P t).normalized)).matrix basis basis
        else 0).re := by
      rw [beforeMeasurement_localDensity P t state promised]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (outputBasisEquiv t n).sum_comp (fun basis : Fin (2 ^ (t + n)) =>
        if CShape.Value.bits ((qpeMeasurement t n).readout basis) = output then
          (DensityOperator.ofPure ((qpeEvolvedState P t).normalized)).matrix basis basis else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted : CShape.Value.bits ((qpeMeasurement t n).readout basis) = output
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

end

end QuantumAlg.QuantumPhaseEstimation
