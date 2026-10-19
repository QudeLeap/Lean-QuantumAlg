/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Matrix
import all QuantumAlg.Primitives.WalshHadamard.Native

/-!
# Exact amplitudes of the actual numerator Hadamard and Z writes

Every entry below comes from the actual placed Hadamard and the existing
measurement interpreter. The original X/A/history prefix and both external
reference coordinates remain explicit. Actual final stores determine the
measurement weights, including their zero-probability branches
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorHadamardMatrix

noncomputable section

variable {environment : OracleModel.empty.Interpretation}
  {runtimeEnvironment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation
open NumeratorResetMatrix

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The native Hadamard amplitude preserves the complete unmeasured prefix. -/
def amplitude (width : Nat) (row column : (context width).register.Index) : ℂ :=
  if framePrefix width row = framePrefix width column then
    WalshHadamard.invSqrtCard width *
      WalshHadamard.walshSign (word width row) (word width column)
  else 0

/-- The actual placed Hadamard has exactly the stated amplitude on every complete basis pair. -/
lemma hadamard_entry (width : Nat) (row column : (context width).register.Index) :
    ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix environment) row
      column =
      amplitude width row column := by
  have native : ((Gate.HadamardLayer.circuit .empty width).binaryMatrix environment) =
      WalshHadamard.hadamardLayerOperator width :=
    WalshHadamard.Native.native_binary_matrix .empty width environment
  have flat : ((NumeratorReset.hadamardMember width).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits (encoding width).width)).tensor
        (WalshHadamard.hadamardLayerOperator width) := by
    change ((UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
      (Gate.HadamardLayer.circuit .empty width)).binaryMatrix environment) = _
    exact (UnitaryCircuit.onCanonicalBinarySuffix_binaryMatrix (encoding width).width
      (Gate.HadamardLayer.circuit .empty width) environment).trans
        (congrArg ((1 : UnitaryOperator (Qubits (encoding width).width)).tensor) native)
  rw [NumeratorRuntime.program_binary_matrix]
  have actual := congrArg
    (fun op : UnitaryOperator (Qubits ((encoding width).width + width)) =>
      op (frameBasis width row) (frameBasis width column)) flat
  refine (actual.trans (UnitaryOperator.tensor_apply
    (1 : UnitaryOperator (Qubits (encoding width).width))
    (WalshHadamard.hadamardLayerOperator width)
    (frameBasis width row) (frameBasis width column))).trans ?_
  have identityEntry : (1 : UnitaryOperator (Qubits (encoding width).width))
      (framePrefix width row) (framePrefix width column) =
      if framePrefix width row = framePrefix width column then (1 : ℂ) else 0 :=
    Matrix.one_apply
  have hadamardEntry := WalshHadamard.hadamardLayerOperator_apply width
    (word width row) (word width column)
  refine (congrArg₂ (fun left right : ℂ => left * right) identityEntry hadamardEntry).trans ?_
  by_cases same : framePrefix width row = framePrefix width column <;>
    simp only [amplitude, same, if_true, if_false, one_mul, zero_mul]

/-- The actual Hadamard preserves classical stores while acting on their full reference blocks. -/
lemma hadamard_weighted_entry (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (weight : Store (context width) → ℂ)
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((NumeratorReset.hadamard width).execute runtimeEnvironment Reference state) (fun entry =>
        weight entry.1)
        (left, leftRef) (right, rightRef) =
      ∑ original : Store (context width) ×
          (ClassicalOracleModel.empty.HiddenState × History), weight original.1 *
        (∑ column : (context width).register.Index,
          (∑ row : (context width).register.Index, amplitude width left row *
            (state.block original).matrix (row, leftRef) (column, rightRef)) *
          star (amplitude width right column)) := by
  rw [NumeratorReset.hadamard, NumeratorRuntime.code, Circuit.execute_unitary]
  refine (@ExecutionState.weightedMatrixEntry_mapClassical
    (Store (context width) × (ClassicalOracleModel.empty.HiddenState × History))
    (Store (context width) × (ClassicalOracleModel.empty.HiddenState × (History × Unit)))
      _ _ _ _
    (state.applyUnitary (fun _ => UnitaryOperator.prodTensor
      ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
        runtimeEnvironment.quantum)
      (1 : UnitaryOperator Reference)))
    (fun value => (value.1, (value.2.1, (value.2.2, ()))))
    (fun value => weight value.1)
    (left, leftRef) (right, rightRef)).trans ?_
  simp only [ExecutionState.weightedMatrixEntry,
    ExecutionState.applyUnitary_block, DensityOperator.localUnitary_block,
    Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, hadamard_entry]

/-- Each actual stored H/Z branch retains the exact two-sided input-dependent characters. -/
lemma measured_entry (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index) :
    (NumeratorMeasuredSupport.density runtimeEnvironment width
      ((NumeratorReset.hadamard width).execute runtimeEnvironment Reference state) stored).matrix
        (left, leftRef) (right, rightRef) =
      if word width left = word width right then
        ∑ original : Store (context width) ×
            (ClassicalOracleModel.empty.HiddenState × History),
          (if Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
            (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
            (readouts width) original.1
            (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
              (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
              (readouts width) left) = stored then (1 : ℂ) else 0) *
          (∑ column : (context width).register.Index,
            (∑ row : (context width).register.Index, amplitude width left row *
              (state.block original).matrix (row, leftRef) (column, rightRef)) *
            star (amplitude width right column))
      else 0 := by
  rw [NumeratorMeasuredSupport.matrix_entry]
  by_cases same : word width left = word width right
  · rw [if_pos same, if_pos same]
    exact hadamard_weighted_entry width state
      (fun original => if Circuit.writeMeasurementPath (allowAllocation := true)
        (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width) original
        (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          (readouts width) left) = stored then 1 else 0)
      left right leftRef rightRef
  · simp only [same, if_false]

end

end QuantumAlg.MeasuredUncompute.NumeratorHadamardMatrix
