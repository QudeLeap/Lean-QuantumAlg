/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Identity operators for the actual empty feedback branch -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma tensor_one (R S : Register) :
    UnitaryOperator.prodTensor (1 : UnitaryOperator R) (1 : UnitaryOperator S) = 1 := by
  apply Subtype.ext
  ext left right
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  change (if left.1 = right.1 then (1 : ℂ) else 0) *
      (if left.2 = right.2 then (1 : ℂ) else 0) =
    if left = right then 1 else 0
  have pair : left = right ↔ left.1 = right.1 ∧ left.2 = right.2 :=
    ⟨fun same => ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩,
      fun same => Prod.ext same.1 same.2⟩
  by_cases first : left.1 = right.1 <;> by_cases second : left.2 = right.2 <;>
    simp [pair, first, second]

private lemma applyUnitary_one {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) :
    state.applyUnitary (fun _ => 1) = state := by
  apply ExecutionState.ext
  intro entry
  exact DensityOperator.applyUnitary_one (state.block entry)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
