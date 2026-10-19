/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Unitary
import all QuantumAlg.Core.Base.Gate.Effect.Average
import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Random

/-!
# Block observations through the existing execution-state operations

These trace identities use the actual classical pushforward, selected blocks,
finite sum and unitary evolution. The observable remains a certified positive
contraction; no state transition or interpreter is introduced here.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] {R : Register}

/-- Observation pullback is independent of the decision procedure used by the real write. -/
lemma effectWeight_mapClassical_decision (decision : DecidableEq D)
    (state : ExecutionState C R) (update : C → D) (effects : D → Effect R) :
    (@mapClassical C D _ _ R decision state update).effectWeight effects =
      state.effectWeight (fun value => effects (update value)) := by
  rw [Subsingleton.elim decision (Classical.decEq D)]
  exact effectWeight_mapClassical state update effects

/-- Each actual classical block pulls its observable through its selected unitary. -/
lemma effectWeight_applyUnitary (state : ExecutionState C R)
    (operator : C → UnitaryOperator R) (effects : C → Effect R) :
    (state.applyUnitary operator).effectWeight effects =
      state.effectWeight (fun value =>
        Effect.pullbackUnitary (operator value) (effects value)) := by
  simp only [effectWeight, applyUnitary_block, Effect.weight_pullbackUnitary]

/-- Actual uniform classical sampling pulls back outcome-dependent effects by its real average. -/
lemma effectWeight_uniformChoice (state : ExecutionState C R) (count : ℕ+)
    (effects : C × Fin count → Effect R) :
    (Execution.uniformChoice state count).effectWeight effects =
      state.effectWeight (fun original =>
        Effect.uniformAverage (fun outcome : Fin count => effects (original, outcome))) := by
  simp only [effectWeight, Fintype.sum_prod_type, Effect.uniformAverage_weight,
    Fintype.card_fin]
  simp only [Effect.weight, Execution.uniformChoice_block_matrix,
    Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Finset.mul_sum]

/-- Observing an actual finite sum adds the observations of its probability-bearing parts. -/
lemma effectWeight_finiteSum {Index : Type} [Fintype Index]
    (parts : Index → ExecutionState C R) (total : ∑ index, (parts index).mass ≤ 1)
    (effects : C → Effect R) :
    (finiteSum parts total).effectWeight effects =
      ∑ index, (parts index).effectWeight effects := by
  simp only [effectWeight, Effect.weight, finiteSum_block_matrix, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]

/-- A selected classical part contributes exactly the blocks in its actual read fiber. -/
lemma effectWeight_selectClassical {Value : Type} [DecidableEq Value]
    (state : ExecutionState C R) (read : C → Value) (value : Value)
    (effects : C → Effect R) :
    (state.selectClassical read value).effectWeight effects =
      ∑ original, if read original = value then (effects original).weight (state.block original)
        else 0 := by
  unfold effectWeight
  apply Finset.sum_congr rfl
  intro original _
  unfold Effect.weight
  rw [selectClassical_block]
  split_ifs <;> simp

end

end QuantumAlg.ExecutionState
