/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Local
import all QuantumAlg.Core.Execution.State.Pure
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Actual bank reset on every complete classical and history record

The full physical bank has the same predetermined zero label on every
complete output Store, hidden service state and measurement history. Each
record retains its actual conditional external-reference matrix, including
off-diagonal entries and zero-mass records. No input seed or normalization
is assumed, and the result does not claim that the surviving records agree.
-/

namespace QuantumAlg.ZReset.Bank

noncomputable section

open Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {allowAllocation : Bool} {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}
  {environment : (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}
  (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
  (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)
  {Reference : Register} {History : Type} [Fintype History]
  (state : State ctx Reference
    ((ExecutionModel.quantum AlgorithmGate.model oracles operations services).HiddenState ×
      History))

/-- The same fixed local zero ket occurs at each complete actual record's mass. -/
lemma zResetBank_block_pure
    (record : Store ctx ×
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations services).HiddenState ×
        (History × (code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).Path))) :
    (StatePromise.pure (NormalizedVector.ket (R := ctx.register)
      ctx.quantumLayout.zeroLabel)).Holds
        (((code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).execute
            ⟨environment.quantum, environment.classical⟩
              Reference state).block record).marginalLeft :=
  ExecutionState.block_pureKet_of_localMarginal
    ((code (allowAllocation := allowAllocation) (oracles := oracles)
      qubits scratch operations services).execute
        ⟨environment.quantum, environment.classical⟩ Reference state)
    ctx.quantumLayout.zeroLabel
    (zResetBank_localDensity_pure (allowAllocation := allowAllocation)
      qubits scratch operations state) record

/-- Every complete actual record keeps its own full reference coefficient at zero. -/
lemma zResetBank_block_entry
    (record : Store ctx ×
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations services).HiddenState ×
        (History × (code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((code (allowAllocation := allowAllocation) (oracles := oracles)
      qubits scratch operations services).execute
        ⟨environment.quantum, environment.classical⟩ Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        (((code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).execute
            ⟨environment.quantum, environment.classical⟩ Reference state).block record).matrix
            (ctx.quantumLayout.zeroLabel, refLeft) (ctx.quantumLayout.zeroLabel, refRight)
      else 0 := by
  let joint := ((code (allowAllocation := allowAllocation) (oracles := oracles)
    qubits scratch operations services).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).block record
  have promised := zResetBank_block_pure (environment := environment)
    (allowAllocation := allowAllocation)
    qubits scratch operations state record
  change joint.marginalLeft.matrix = joint.marginalLeft.mass •
    (DensityOperator.ofPure (NormalizedVector.ket ctx.quantumLayout.zeroLabel)).matrix
      at promised
  have rowZero (row : ctx.quantumLayout.Basis) (outside : row ≠ ctx.quantumLayout.zeroLabel)
      (column : ctx.quantumLayout.Basis) (rowRef columnRef : Reference.Index) :
      joint.matrix (row, rowRef) (column, columnRef) = 0 := by
    have localZero : joint.marginalLeft.matrix row row = 0 := by
      rw [promised, Matrix.smul_apply, DensityOperator.ofPure_matrix]
      simp only [NormalizedVector.ket_apply, if_neg outside, zero_mul, smul_zero]
    have jointZero := DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
      joint row localZero rowRef
    exact DensityOperator.row_zero_of_diagonal_zero joint (row, rowRef) jointZero
      (column, columnRef)
  by_cases sameLeft : left = ctx.quantumLayout.zeroLabel
  · subst left
    by_cases sameRight : right = ctx.quantumLayout.zeroLabel
    · subst right
      simp only [and_self, if_true]
    · simp only [sameRight, and_false, if_false]
      change joint.matrix (ctx.quantumLayout.zeroLabel, refLeft) (right, refRight) = 0
      exact DensityOperator.column_zero_of_diagonal_zero joint (right, refRight)
        (rowZero right sameRight right refRight refRight)
        (ctx.quantumLayout.zeroLabel, refLeft)
  · simp only [sameLeft, false_and, if_false]
    exact rowZero left sameLeft right refLeft refRight

/-- The local zero ket factors from each actual record's complete reference coefficient. -/
lemma zResetBank_block_factor
    (record : Store ctx ×
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations services).HiddenState ×
        (History × (code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((code (allowAllocation := allowAllocation) (oracles := oracles)
      qubits scratch operations services).execute
        ⟨environment.quantum, environment.classical⟩ Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel left *
        (((code (allowAllocation := allowAllocation) (oracles := oracles)
          qubits scratch operations services).execute
            ⟨environment.quantum, environment.classical⟩ Reference state).block record).matrix
            (ctx.quantumLayout.zeroLabel, refLeft) (ctx.quantumLayout.zeroLabel, refRight) *
        star (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel right) :=
  (zResetBank_block_entry (allowAllocation := allowAllocation)
    qubits scratch operations state record left right refLeft refRight).trans
    (BasisSeeded.ket_factor (R := ctx.register) ctx.quantumLayout.zeroLabel left right _).symm

end

end QuantumAlg.ZReset.Bank
