/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Circuit
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Per-record operators of the actual physical measurement/reset circuit

The operator below comes from the executed H, actual measured projector and
the selected reset's proved native matrix. The block equation retains every
original Store/history fiber and all off-diagonal reference entries. It does
not replace execution by a supplied channel [G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

open scoped BigOperators

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

/-- Operator of one actual measured outcome, including H and its physical reset. -/
def krausOperator (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (environment : oracles.Interpretation)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor (QuditShift.operator ctx.quantumLayout wire (-outcome))
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
    ZMeasurement.projector
      (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire) outcome *
      (UnitaryOperator.prodTensor ((hadamard wire qubit).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference))

/-- Every complete actual output block is the exact sum of its original record-conditioned branches.
In particular the result-cell overwrite never discards colliding input stores. -/
lemma execute_block_matrix {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {allowAllocation : Bool}
    (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (circuit (oracles := oracles) wire qubit output operations services
        allowAllocation).Path)))
    (left right : (Register.prod ctx.register Reference).Index) :
    (((circuit wire qubit output operations services allowAllocation).execute
      environment Reference state).block result).matrix left right =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome,
        if record (oracles := oracles) wire qubit output operations services original outcome =
            result then
          (krausOperator wire qubit environment.quantum outcome Reference *
            (state.block original).matrix *
              (krausOperator wire qubit environment.quantum outcome Reference).conjTranspose)
                left right
        else 0 := by
  rw [execute, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs
  · rw [ExecutionState.measureZ_block]
    simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
      ZMeasurement.branch, krausOperator,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rfl

end

end QuantumAlg.EncodedBit.MeasuredUncompute
