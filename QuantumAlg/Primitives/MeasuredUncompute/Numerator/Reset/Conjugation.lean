/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Projection

/-!
# Exact full-state matrix of the actual H/Z/stored-X sequence

The actual final store determines both its original classical fibers and
the native X sequence that is executed. This equality factors that same
interpreter result into its existing Hadamard, Z projection, and selected
reset matrices, retaining every external-reference entry and every prefix
coordinate [LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorResetConjugation

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem source_hadamard (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width)) :
    NumeratorStoredProjection.source width
      ((NumeratorReset.hadamard width).execute Reference state) stored =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
          (1 : UnitaryOperator Reference))
        (NumeratorStoredProjection.source width state stored) :=
  Circuit.unitary_store_filter
    (NumeratorRuntime.program width (NumeratorReset.hadamardMember width))
    state
    (fun original => Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored)

/-- The actual H/Z/reset state keeps exactly its selected source fiber and complete reference. -/
theorem actual_density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical ((NumeratorReset.code width).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (NumeratorRuntime.program width
            (NumeratorReset.member width (stored.read (input width)))).matrix
          (1 : UnitaryOperator Reference))
        (ZMeasurement.branch
          (fun entry : (Register.prod (context width).register Reference).Index =>
            word width entry.1)
          (NumeratorReset.outcome (stored.read (input width)))
          (DensityOperator.applyUnitary
            (UnitaryOperator.prodTensor
              (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
              (1 : UnitaryOperator Reference))
            (NumeratorStoredProjection.source width state stored))) := by
  rw [NumeratorReset.code, Circuit.seq_store_marginal, NumeratorResetMatrix.actual_density]
  unfold NumeratorResetMatrix.density
  rw [NumeratorStoredProjection.actual_density, source_hadamard]

/-- This matrix product records the same three actual steps for the actual stored word. -/
def operator (width : Nat) (Reference : Register) (stored : Store (context width)) :
    HilbertOperator (Register.prod (context width).register Reference) :=
  (UnitaryOperator.prodTensor
      (NumeratorRuntime.program width
        (NumeratorReset.member width (stored.read (input width)))).matrix
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference)) *
    ZMeasurement.projector
      (fun entry : (Register.prod (context width).register Reference).Index =>
            word width entry.1)
      (NumeratorReset.outcome (stored.read (input width))) *
    (UnitaryOperator.prodTensor
      (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference))

/-- Full conjugation is an equality of the actual retained-store block, not a separate execution. -/
theorem actual_matrix (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical ((NumeratorReset.code width).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      operator width Reference stored *
        (NumeratorStoredProjection.source width state stored).matrix *
        (operator width Reference stored).conjTranspose := by
  rw [actual_density]
  simp only [DensityOperator.applyUnitary_matrix, ZMeasurement.branch, operator,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.MeasuredUncompute.NumeratorResetConjugation
