/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage.Laws
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution.Laws
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.WalshHadamard

/-!
# The probability of the actual Walsh-Hadamard query readout output

The final classical read selects blocks of the single circuit execution.
The exact measurement-write fiber, followed by the actual packing opcode,
reduces their masses to the Born fibers of the original final vector. All
unmeasured target and external-reference coordinates are summed. The
mathematical readout distribution is therefore a proved observation of this
execution, not a supplied implementation parameter.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

private lemma packedRead (n : Nat) (store : Store (post n)) :
    (store.write (BitWord.application (packing n)).output
      ((packing n).eval (store.read (BitWord.application (packing n)).input))).read
        (.storage (resultRef n).toCStorageRef) =
      (packing n).eval (store.read (MeasurementCells.input (resultContext n) 2 n)) :=
  Store.read_applyOp_output store (packing n)

/-- The actual measured and packed output has precisely the corresponding initial diagonal fiber. -/
lemma readoutCode_block_mass {n : Nat} (function : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post n) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (output : CShape.Value (.bits n)) :
    ((((readoutCode n).execute (environment function) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef n).toCStorageRef))).block output).mass =
      (∑ basis : (post n).register.Index,
        if CShape.Value.bits ((measurement n).readout (outputBasisEquiv n basis)) = output then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.execute_classical_mapClassical (model := model n) (environment function)
    (BitWord.application (packing n))
    (packing n).eval (BitWord.bitWord_application_evaluate (packing n))]
  simp only [ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.measurementSequence_diagonalSum]
  simp only [packedRead, packing_measured_value]
  calc
    _ = ∑ basis : (post n).register.Index,
        (if CShape.Value.bits ((measurement n).readout (outputBasisEquiv n basis)) = output
          then (1 : ℂ) else 0) * state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if CShape.Value.bits ((measurement n).readout (outputBasisEquiv n basis)) = output
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

/-- Every final output-block mass is the original query-readout Born fiber,
derived from actual preparation, gates, measurements, storage writes and packing. -/
lemma code_block_mass {n : Nat} (f : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H))
    (normalized : state.IsNormalized) (output : CShape.Value (.bits n)) :
    ((((code n).execute (environment f) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef n).toCStorageRef))).block output).mass =
      ∑ basis : Fin (2 ^ (n + 1)),
        if CShape.Value.bits ((measurement n).readout basis) = output then
          ‖WalshHadamard.finalJointState f basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post n).register.Index,
        if CShape.Value.bits ((measurement n).readout (outputBasisEquiv n basis)) = output then
          ((beforeMeasurement n).execute (environment f)
            Reference state).quantumMarginal.marginalLeft.matrix
            basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def] using
          readoutCode_block_mass f ((beforeMeasurement n).execute (environment f)
            Reference state) output
    _ = (∑ basis : Fin (2 ^ (n + 1)),
        if CShape.Value.bits ((measurement n).readout basis) = output then
          (DensityOperator.ofPure (WalshHadamard.finalJointState f)).matrix basis basis
        else 0).re := by
      rw [beforeMeasurement_localDensity f state normalized]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (outputBasisEquiv n).sum_comp (fun basis : Fin (2 ^ (n + 1)) =>
        if CShape.Value.bits ((measurement n).readout basis) = output then
          (DensityOperator.ofPure (WalshHadamard.finalJointState f)).matrix basis basis else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted : CShape.Value.bits ((measurement n).readout basis) = output
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

end

end QuantumAlg.WalshHadamard.Readout
