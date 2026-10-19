/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Components.Classical.Model.BitWord.Execution

import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Storage.Laws
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Execution.Laws
import all QuantumAlg.Algorithms.Grover.Elementary.Laws
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Measure.Distribution

/-!
# The Born fibers of Grover's actual output store

Actual preparation, the original unitary, every Z write and the closed
packing instruction determine each final output block. Summing the same
interpreter's classical histories and external-reference coordinates gives
the Born fiber of the exact evolved Grover vector. This is a proof of the
execution's output distribution, never an independent PMF parameter.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

private lemma packedRead (n k : Nat) (store : Store (post n k)) :
    (store.write (BitWord.application (packing n k)).output
      ((packing n k).eval (store.read (BitWord.application (packing n k)).input))).read
        (.storage (resultRef n k).toCStorageRef) =
      (packing n k).eval (store.read (MeasurementCells.input (resultContext n k) 2 n)) :=
  Store.read_applyOp_output store (packing n k)

/-- The actual measured and packed output has precisely the corresponding initial diagonal fiber. -/
lemma readoutCode_block_mass (n k : Nat) (actual : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post n k) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (output : CShape.Value (.bits n)) :
    ((((readoutCode n k).execute actual Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef n k).toCStorageRef))).block output).mass =
      (∑ basis : (post n k).register.Index,
        if CShape.Value.bits ((zMeasure (layout n)).readout (outputSource n k basis)) = output
          then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.execute_classical_mapClassical (model := model n)
    (environment := actual)
    (BitWord.application (packing n k))
    (packing n k).eval (BitWord.bitWord_application_evaluate (packing n k))]
  simp only [ExecutionState.diagonalSum_mapClassical]
  rw [Circuit.measurementSequence_diagonalSum]
  simp only [packedRead, packing_measured_value]
  calc
    _ = ∑ basis : (post n k).register.Index,
        (if CShape.Value.bits ((zMeasure (layout n)).readout (outputSource n k basis)) = output
          then (1 : ℂ) else 0) * state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if CShape.Value.bits ((zMeasure (layout n)).readout (outputSource n k basis)) = output
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

private lemma evolved_product_diagonal {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (source : Fin (2 ^ n)) (work : Fin (2 ^ (helperWidth n k))) :
    ((DensityOperator.ofPure (Elementary.evolvedVector marked k)).matrix
      (prodEquiv (source, work)) (prodEquiv (source, work))).re =
        if work = 0 then ‖(evolvedState marked k).normalized source‖ ^ 2 else 0 := by
  rw [pure_diagonal_re]
  change ‖(evolvedState marked k).normalized.tensor
      (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)
      (prodEquiv (source, work))‖ ^ 2 = _
  rw [NormalizedVector.tensor_apply_prod, NormalizedVector.ket_apply]
  by_cases zero : work = 0
  · simp only [zero, if_true, mul_one]
  · simp only [zero, if_false, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Every final output-block mass is the original query-readout Born fiber,
derived from actual elementary gates and measured source wires, with the work wire retained. -/
lemma code_block_mass {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H))
    (normalized : state.IsNormalized) (output : CShape.Value (.bits n)) :
    ((((code n k).execute (environment marked) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef n k).toCStorageRef))).block output).mass =
      ∑ basis : Fin (2 ^ n),
        if CShape.Value.bits ((zMeasure (layout n)).readout basis) = output then
          ‖(evolvedState marked k).normalized basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post n k).register.Index,
        if CShape.Value.bits ((zMeasure (layout n)).readout (outputSource n k basis)) = output
          then
          ((beforeMeasurement n k).execute
          (environment marked) Reference state).quantumMarginal.marginalLeft.matrix
            basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def] using
          readoutCode_block_mass n k (environment marked)
            ((beforeMeasurement n k).execute (environment marked) Reference state) output
    _ = (∑ basis : Fin (2 ^ (totalQubits n k)),
        if CShape.Value.bits ((zMeasure (layout n)).readout
            (((prodEquiv (m := n) (n := helperWidth n k)).symm basis).1)) = output
          then (DensityOperator.ofPure (Elementary.evolvedVector marked k)).matrix basis basis
          else 0).re := by
      rw [beforeMeasurement_localDensity marked k state normalized]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm, outputSource]
      exact (outputBasisEquiv n k).sum_comp
        (fun basis : Fin (2 ^ (totalQubits n k)) =>
          if CShape.Value.bits ((zMeasure (layout n)).readout
              (((prodEquiv (m := n) (n := helperWidth n k)).symm basis).1)) = output
            then (DensityOperator.ofPure (Elementary.evolvedVector marked k)).matrix basis basis
            else (0 : ℂ))
    _ = (∑ pair : Fin (2 ^ n) × Fin (2 ^ (helperWidth n k)),
        if CShape.Value.bits ((zMeasure (layout n)).readout pair.1) = output
          then (DensityOperator.ofPure (Elementary.evolvedVector marked k)).matrix
            (prodEquiv pair) (prodEquiv pair) else 0).re := by
      apply congrArg Complex.re
      let joined : Fin (2 ^ n) × Fin (2 ^ (helperWidth n k)) ≃
          Fin (2 ^ (totalQubits n k)) := prodEquiv
      have reindexed := joined.sum_comp
        (fun basis : Fin (2 ^ (totalQubits n k)) =>
          if CShape.Value.bits ((zMeasure (layout n)).readout (joined.symm basis).1) = output
            then (DensityOperator.ofPure (Elementary.evolvedVector marked k)).matrix basis basis
            else (0 : ℂ))
      refine reindexed.symm.trans ?_
      apply Finset.sum_congr rfl
      intro pair _
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Complex.re_sum, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro source _
      by_cases accepted : CShape.Value.bits ((zMeasure (layout n)).readout source) = output
      · simp only [accepted, if_true, evolved_product_diagonal]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      · simp only [accepted, if_false, Complex.zero_re, Finset.sum_const_zero]

end

end QuantumAlg.GroverSearch
