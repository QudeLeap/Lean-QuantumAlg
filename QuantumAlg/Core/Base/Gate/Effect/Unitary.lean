/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect

/-!
# Positive effects pulled back through unitary evolution

The pulled observable is the conjugate of the same certified unitary acting
on the density operator. Its positivity and vector contraction are proved
from that conjugation, and its trace weight agrees on every mixed input.
-/

open scoped ComplexOrder

namespace QuantumAlg.Effect

noncomputable section

variable {R : Register}

/-- Pull an observable back through the same unitary density evolution. -/
def pullbackUnitary (operator : UnitaryOperator R) (effect : Effect R) : Effect R where
  matrix := (operator : HilbertOperator R).conjTranspose * effect.matrix *
    (operator : HilbertOperator R)
  positive := effect.positive.conjTranspose_mul_mul_same (operator : HilbertOperator R)
  contractive vector := by
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
    rw [← UnitaryOperator.coe_dagger]
    change ‖operator.dagger.applyVec (effect.matrix.applyVec (operator.applyVec vector))‖ ≤ _
    rw [UnitaryOperator.norm_applyVec]
    exact (effect.contractive (operator.applyVec vector)).trans_eq (operator.norm_applyVec vector)

/-- Unitary pullback has the exact trace weight of the actual density conjugation. -/
theorem weight_pullbackUnitary (operator : UnitaryOperator R) (effect : Effect R)
    (state : DensityOperator R) :
    (pullbackUnitary operator effect).weight state =
      effect.weight (DensityOperator.applyUnitary operator state) := by
  unfold weight pullbackUnitary
  rw [DensityOperator.applyUnitary_matrix]
  congr 1
  calc
    _ = ((operator : HilbertOperator R).conjTranspose *
      (effect.matrix * ((operator : HilbertOperator R) * state.matrix))).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((effect.matrix * ((operator : HilbertOperator R) * state.matrix)) *
      (operator : HilbertOperator R).conjTranspose).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end

end QuantumAlg.Effect
