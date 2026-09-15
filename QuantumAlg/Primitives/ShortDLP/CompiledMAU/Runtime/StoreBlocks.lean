/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Selected
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# The actual selected operator on each complete stored parameter block

Fixing the complete actual store also fixes the parameter read by the branch.
The selected member therefore conjugates that entire store-reference block
by one known source member. The block may have arbitrary quantum/reference
correlations and arbitrary probability mass; no factorization is assumed.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- One actual store selects one exact unitary on its complete reference-correlated block. -/
theorem shortDLP_runtimeSelected_store_unitary {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    (ExecutionState.filterClassical
      ((selected m ell width sameWires parameter N generator target).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (RuntimePlacement.memberProgram m ell width sameWires N
            (generator (original.read parameter)) (target (original.read parameter))).matrix
          (1 : UnitaryOperator Reference))
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix := by
  let part := state.filterClassical (fun entry => entry.1 = original)
  let chosen := UnitaryOperator.prodTensor
    (RuntimePlacement.memberProgram m ell width sameWires N
      (generator (original.read parameter)) (target (original.read parameter))).matrix
    (1 : UnitaryOperator Reference)
  have fixed (entry : Store ctx × History) :
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (RuntimePlacement.memberProgram m ell width sameWires N
            (generator (entry.1.read parameter)) (target (entry.1.read parameter))).matrix
          (1 : UnitaryOperator Reference)) (part.block entry)).matrix =
        (DensityOperator.applyUnitary chosen (part.block entry)).matrix := by
    by_cases same : entry.1 = original
    · simp only [same, chosen]
    · simp only [part, ExecutionState.filterClassical_block, same, if_false,
        DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
        Matrix.mul_zero, Matrix.zero_mul]
  have selection := shortDLP_runtimeSelected_joint_matrix m ell width sameWires parameter N
    generator target (fun store => store = original) state
  have constant := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun entry _ => fixed entry)
  have combined := congrArg DensityOperator.matrix
    (ExecutionState.fixedUnitary_quantumMarginal part chosen)
  exact selection.trans (constant.trans combined)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
