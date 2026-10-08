/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Untouched references under actual local unitary execution

Each local instruction acts as its declared unitary tensored with the identity
on the external reference. Unitary conjugation [dW19, qcnotes.tex:5405] and
partial trace [dW19, qcnotes.tex:5381] preserve every reference matrix entry,
including off-diagonal entries of a state correlated with the local input.
These supporting matrix equations introduce no runtime resources or new
execution operation.
-/

namespace QuantumAlg.DensityOperator
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

theorem localUnitary_block {R Reference : Register} (U : UnitaryOperator R)
    (state : DensityOperator (Register.prod R Reference))
    (left right : R.Index) (refLeft refRight : Reference.Index) :
    (applyUnitary (UnitaryOperator.prodTensor U (1 : UnitaryOperator Reference)) state).matrix
      (left, refLeft) (right, refRight) =
    ((U : HilbertOperator R) *
      state.matrix.submatrix (fun i => (i, refLeft)) (fun j => (j, refRight)) *
      (U : HilbertOperator R).conjTranspose) left right := by
  simp only [applyUnitary_matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    UnitaryOperator.prodTensor_apply]
  change (∑ b : R.Index × Reference.Index,
    (∑ a : R.Index × Reference.Index,
      (U left a.1 * (1 : HilbertOperator Reference) refLeft a.2) * state.matrix a b) *
      star (U right b.1 * (1 : HilbertOperator Reference) refRight b.2)) = _
  simp [Fintype.sum_prod_type, Matrix.one_apply, apply_ite]


/-- Local unitary execution preserves every matrix entry of the untouched reference marginal. -/
theorem localUnitary_reference_entry {R Reference : Register} (U : UnitaryOperator R)
    (state : DensityOperator (Register.prod R Reference))
    (refLeft refRight : Reference.Index) :
    (∑ i : R.Index,
      (applyUnitary (UnitaryOperator.prodTensor U (1 : UnitaryOperator Reference)) state).matrix
        (i, refLeft) (i, refRight)) =
    ∑ i : R.Index, state.matrix (i, refLeft) (i, refRight) := by
  simp_rw [localUnitary_block]
  exact trace_unitary_conjugation U
    (state.matrix.submatrix (fun i => (i, refLeft)) (fun j => (j, refRight)))

end
end QuantumAlg.DensityOperator

namespace QuantumAlg.ExecutionState

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A stored-value-dependent local unitary also preserves every untouched reference entry. -/
theorem applyLocalUnitary_reference_entry {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (program : C → UnitaryOperator R)
    (refLeft refRight : Reference.Index) :
    (∑ i : R.Index,
      (state.applyUnitary (fun value => UnitaryOperator.prodTensor (program value)
        (1 : UnitaryOperator Reference))).quantumMarginal.matrix
          (i, refLeft) (i, refRight)) =
      ∑ i : R.Index, state.quantumMarginal.matrix (i, refLeft) (i, refRight) := by
  change (∑ i : R.Index,
    (∑ value : C, (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Reference))
      (state.block value)).matrix) (i, refLeft) (i, refRight)) =
    ∑ i : R.Index, (∑ value : C, (state.block value).matrix) (i, refLeft) (i, refRight)
  simp only [Matrix.sum_apply]
  calc
    _ = ∑ value : C, ∑ i : R.Index,
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Reference))
          (state.block value)).matrix (i, refLeft) (i, refRight) := Finset.sum_comm
    _ = ∑ value : C, ∑ i : R.Index,
        (state.block value).matrix (i, refLeft) (i, refRight) :=
      Finset.sum_congr rfl fun value _ =>
        DensityOperator.localUnitary_reference_entry (program value) (state.block value)
          refLeft refRight
    _ = _ := Finset.sum_comm

end

end QuantumAlg.ExecutionState

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual circuit interpreter leaves every external reference matrix entry unchanged. -/
theorem unitary_reference_entry {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} {Reference : Register}
    {H : Type} [Fintype H] (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : Execution.State ctx Reference (classicalOracles.HiddenState × H))
    (refLeft refRight : Reference.Index) :
    (∑ i : ctx.register.Index,
      ((Circuit.unitary (operations := operations) (classicalOracles := classicalOracles)
        program).execute Reference state).quantumMarginal.matrix
        (i, refLeft) (i, refRight)) =
      ∑ i : ctx.register.Index, state.quantumMarginal.matrix (i, refLeft) (i, refRight) := by
  rw [execute_unitary]
  simp only [ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.applyLocalUnitary_reference_entry state (fun _ => program.matrix)
    refLeft refRight

end

end QuantumAlg.Circuit
