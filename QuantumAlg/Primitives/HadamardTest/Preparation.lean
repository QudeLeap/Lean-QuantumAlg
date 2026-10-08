/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The actual prepared and evolved Hadamard-test state

The real fresh-control preparation and unitary instructions yield the source
state in the complete physical runtime coordinates. Only the original local
input is prescribed; the calculation sums every external-reference block
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

def sourceInput {width : Nat} (input : NormalizedVector (Qubits width)) :
    NormalizedVector (Qubits (1 + width)) := NormalizedVector.ket0.tensor input

def evolvedState {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : NormalizedVector (Qubits (1 + width)) :=
  (hadamardTest unitary).apply (sourceInput input)

private theorem preparation_basis_value
    (basis : (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.register.Index) :
    (OwnedQubitPrefix.zeroPreparation 1).normalized basis =
      NormalizedVector.ket0 ((OwnedQubitPrefix.prefixLayout 1).binaryIndexEquiv basis) := by
  have physicalZero : (OwnedQubitPrefix.prefixLayout 1).binaryIndexEquiv.symm
      (0 : Fin (2 ^ 1)) = (OwnedQubitPrefix.zeroPreparation 1).value :=
    BinaryBasis.bigEndianEquiv_symm_zero 1
  change NormalizedVector.ket
    (R := (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.register)
    (OwnedQubitPrefix.zeroPreparation 1).value basis = _
  rw [← physicalZero]
  rw [NormalizedVector.ket0, NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  simp only [Equiv.eq_symm_apply]

private theorem source_input_entry {width : Nat} (input : NormalizedVector (Qubits width))
    (newRow newColumn : (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.register.Index)
    (oldRow oldColumn : (pre width).register.Index) :
    ((DensityOperator.ofPure (sourceInput input)).reindex
      (S := (prepared width).register) (OwnedQubitPrefix.basisEquiv 1 width).symm).matrix
        (OwnedQubitPrefix.assembly 1 width (newRow, oldRow))
        (OwnedQubitPrefix.assembly 1 width (newColumn, oldColumn)) =
      ((OwnedQubitPrefix.zeroPreparation 1).normalized newRow *
          star ((OwnedQubitPrefix.zeroPreparation 1).normalized newColumn)) *
        (input (OwnedQubitPrefix.inputBasisEquiv 1 width oldRow) *
          star (input (OwnedQubitPrefix.inputBasisEquiv 1 width oldColumn))) := by
  have inputValue (fresh : (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.register.Index)
      (original : (pre width).register.Index) :
      sourceInput input (OwnedQubitPrefix.basisEquiv 1 width
        (OwnedQubitPrefix.assembly 1 width (fresh, original))) =
        (OwnedQubitPrefix.zeroPreparation 1).normalized fresh *
          input (OwnedQubitPrefix.inputBasisEquiv 1 width original) := by
    rw [OwnedQubitPrefix.basisEquiv_assembly, sourceInput,
      NormalizedVector.tensor_apply_prod, preparation_basis_value]
  rw [DensityOperator.reindex_entry, DensityOperator.ofPure_matrix]
  simp only [Equiv.symm_symm, inputValue, star_mul]
  ring

/-- Actual preparation gives the source's zero-control/input tensor in the physical frame. -/
theorem preparation_localDensity {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (input : NormalizedVector (Qubits width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise input state.quantumMarginal.marginalLeft) :
    ((OwnedQubitPrefix.prepareCode AlgorithmGate.model
      (UnitarySource.model unitary true) 1 width).execute Reference
        state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (sourceInput input)).reindex
        (S := (prepared width).register) (OwnedQubitPrefix.basisEquiv 1 width).symm := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨newRow, oldRow⟩, rfl⟩ := (OwnedQubitPrefix.assembly 1 width).surjective row
  obtain ⟨⟨newColumn, oldColumn⟩, rfl⟩ :=
    (OwnedQubitPrefix.assembly 1 width).surjective column
  rw [source_input_entry]
  calc
    _ = ∑ reference : Reference.Index,
        ((OwnedQubitPrefix.prepareCode AlgorithmGate.model
          (UnitarySource.model unitary true) 1 width).execute Reference
            state).quantumMarginal.matrix
          (OwnedQubitPrefix.assembly 1 width (newRow, oldRow), reference)
          (OwnedQubitPrefix.assembly 1 width (newColumn, oldColumn), reference) :=
      DensityOperator.marginalLeft_matrix _ _ _
    _ = ∑ reference : Reference.Index,
        ((OwnedQubitPrefix.zeroPreparation 1).normalized newRow *
          star ((OwnedQubitPrefix.zeroPreparation 1).normalized newColumn)) *
          state.quantumMarginal.matrix (oldRow, reference) (oldColumn, reference) := by
      apply Finset.sum_congr rfl
      intro reference _
      exact Circuit.prepareZero_joined_entry (gates := AlgorithmGate.model)
        (oracles := UnitarySource.model unitary true) (operations := .empty)
        (classicalOracles := .empty) state ⟨0⟩
        (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
        (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width)
        newRow newColumn (oldRow, reference) (oldColumn, reference)
    _ = ((OwnedQubitPrefix.zeroPreparation 1).normalized newRow *
          star ((OwnedQubitPrefix.zeroPreparation 1).normalized newColumn)) *
        state.quantumMarginal.marginalLeft.matrix oldRow oldColumn := by
      rw [← Finset.mul_sum]
      exact congrArg (fun value : ℂ =>
        ((OwnedQubitPrefix.zeroPreparation 1).normalized newRow *
          star ((OwnedQubitPrefix.zeroPreparation 1).normalized newColumn)) * value)
        (DensityOperator.marginalLeft_matrix (R := (pre width).register) (S := Reference)
          state.quantumMarginal oldRow oldColumn).symm
    _ = _ := congrArg (fun value : ℂ =>
      ((OwnedQubitPrefix.zeroPreparation 1).normalized newRow *
        star ((OwnedQubitPrefix.zeroPreparation 1).normalized newColumn)) * value)
      (promised oldRow oldColumn)

private theorem nativeProgram_input {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) :
    DensityOperator.applyUnitary (nativeProgram unitary).matrix
      ((DensityOperator.ofPure (sourceInput input)).reindex
        (S := (prepared width).register) (OwnedQubitPrefix.basisEquiv 1 width).symm) =
      (DensityOperator.ofPure (evolvedState unitary input)).reindex
        (S := (prepared width).register) (OwnedQubitPrefix.basisEquiv 1 width).symm := by
  rw [nativeProgram_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  rfl

private theorem retain_localDensity {width : Nat}
    (unitary : UnitaryOperator (Qubits width))
    {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (prepared width) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    ((Circuit.retain (model := model unitary) (prepared width)
      ⟨2⟩ (.finite 2) (resultFresh width)).execute
      Reference state).quantumMarginal.marginalLeft = state.quantumMarginal.marginalLeft := by
  simp only [Circuit.execute_retain, ExecutionState.mapClassical_quantumMarginal]

/-- The actual state before its Z write is exactly the source Hadamard-test pure state locally. -/
theorem beforeMeasurement_localDensity {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (input : NormalizedVector (Qubits width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise input state.quantumMarginal.marginalLeft) :
    ((beforeMeasurement unitary).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (evolvedState unitary input)).reindex
        (S := (post width).register) (outputBasisEquiv width).symm := by
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, retain_localDensity unitary,
    Circuit.unitary_localDensity,
    preparation_localDensity unitary input state promised, nativeProgram_input]
  rfl

end

end QuantumAlg.HadamardTest
