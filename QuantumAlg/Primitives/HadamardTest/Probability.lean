/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Preparation
import all QuantumAlg.Primitives.HadamardTest.Coordinates
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Base.Marginal

/-!
# Exact probabilities from the actual Hadamard-test measurement

The stored outcome is obtained from the actual Z write. Summing all classical
histories and reference coordinates gives the source's exact Born formula
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

/-- The retained result has the Born fiber of the physical control that was actually measured. -/
lemma readoutCode_block_mass {width : Nat} (unitary : UnitaryOperator (Qubits width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (output : CShape.Value (.finite 2)) :
    ((((readoutCode width).execute (environment unitary) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef width).toCStorageRef))).block output).mass =
      (∑ basis : (post width).register.Index,
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1 = output then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.measurementSequence_diagonalSum]
  simp only [measured_value width]
  calc
    _ = ∑ basis : (post width).register.Index,
        (if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1 = output then
          (1 : ℂ) else 0) * state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1 = output then
          1 else 0)
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

/-- The complete native code yields precisely the original source state's outcome fibers. -/
lemma code_block_mass {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise input state.quantumMarginal.marginalLeft)
    (output : CShape.Value (.finite 2)) :
    ((((code width).execute (environment unitary) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef width).toCStorageRef))).block output).mass =
      ∑ basis : Fin (2 ^ (1 + width)),
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm basis).1 = output then
          ‖evolvedState unitary input basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post width).register.Index,
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm (outputBasisEquiv width basis)).1 = output then
          ((beforeMeasurement width).execute (environment unitary)
            Reference state).quantumMarginal.marginalLeft.matrix
            basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def] using
          readoutCode_block_mass unitary
            ((beforeMeasurement width).execute (environment unitary) Reference state) output
    _ = (∑ basis : Fin (2 ^ (1 + width)),
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm basis).1 = output then
          (DensityOperator.ofPure (evolvedState unitary input)).matrix basis basis else 0).re := by
      rw [beforeMeasurement_localDensity unitary input state promised]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (outputBasisEquiv width).sum_comp (fun basis : Fin (2 ^ (1 + width)) =>
        if CShape.Value.finite (cardinality := 2)
          ((prodEquiv (m := 1) (n := width)).symm basis).1 = output then
          (DensityOperator.ofPure (evolvedState unitary input)).matrix basis basis else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted :
          CShape.Value.finite (cardinality := 2)
            ((prodEquiv (m := 1) (n := width)).symm basis).1 = output
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

/-- The real stored zero outcome has exactly the registered real-overlap probability. -/
lemma code_zero_mass {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise input state.quantumMarginal.marginalLeft) :
    ((((code width).execute (environment unitary) Reference state).mapClassical
      (fun value => value.1.read (.storage (resultRef width).toCStorageRef))).block
        (.finite 0)).mass = probabilityZero unitary input := by
  rw [code_block_mass unitary input state promised]
  let fiber (basis : Fin (2 ^ (1 + width))) : Real :=
    if CShape.Value.finite (cardinality := 2)
      ((prodEquiv (m := 1) (n := width)).symm basis).1 =
        CShape.Value.finite (cardinality := 2) (0 : Fin 2) then
        ‖evolvedState unitary input basis‖ ^ 2 else 0
  change (∑ basis, fiber basis) = _
  calc
    _ = ∑ pair : Fin (2 ^ 1) × Fin (2 ^ width), fiber (prodEquiv pair) :=
      ((prodEquiv (m := 1) (n := width)).sum_comp fiber).symm
    _ = (evolvedState unitary input).probQubit0 0 := by
      change _ = ∑ value : Fin (2 ^ width),
        ‖evolvedState unitary input (prodEquiv (0, value))‖ ^ 2
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro value _
      change (∑ control : Fin 2, fiber (prodEquiv (control, value))) = _
      rw [Fin.sum_univ_two]
      have different : CShape.Value.finite (cardinality := 2) (1 : Fin 2) ≠
          CShape.Value.finite (cardinality := 2) (0 : Fin 2) := by
        decide
      simp only [fiber, Equiv.symm_apply_apply, if_true, different, if_false, add_zero]
    _ = _ := hadamardTest_probQubit0_zero (U := unitary) input

end

end QuantumAlg.HadamardTest
