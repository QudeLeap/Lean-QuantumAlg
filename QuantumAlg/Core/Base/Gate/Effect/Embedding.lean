/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect
import all QuantumAlg.Core.Base.Gate.SupportHybrid

/-!
# Effects compressed along an injective basis placement

Preparing a definite basis value embeds the previous register into the enlarged
register. Compressing an effect to those actual basis coordinates preserves
positivity and contraction, as witnessed by extension with zero amplitudes.
-/

namespace QuantumAlg.Effect

noncomputable section

open scoped ComplexOrder

variable {R S : Register}

private def extendVector (embedding : S.Index → R.Index) (vector : HilbertVector S) :
    HilbertVector R :=
  ∑ index, vector index • (NormalizedVector.ket (embedding index) : HilbertVector R)

private theorem extendVector_apply (embedding : S.Index → R.Index) (vector : HilbertVector S)
    (output : R.Index) :
    extendVector embedding vector output =
      ∑ index, if embedding index = output then vector index else 0 := by
  classical
  simp [extendVector, NormalizedVector.ket_apply, mul_ite, eq_comm]

private theorem norm_extendVector (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (vector : HilbertVector S) :
    ‖extendVector embedding vector‖ = ‖vector‖ := by
  rw [extendVector, HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq
    Finset.univ embedding injective]
  rw [← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg vector)]

private theorem norm_restrictVector_le (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (vector : HilbertVector R) :
    ‖WithLp.toLp 2 (fun index => vector (embedding index))‖ ≤ ‖vector‖ := by
  classical
  have squared : ‖WithLp.toLp 2 (fun index => vector (embedding index))‖ ^ 2 ≤
      ‖vector‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    rw [← Finset.sum_image (f := fun index => ‖vector index‖ ^ 2)
      (s := Finset.univ) (fun _ _ _ _ equality => injective equality)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg vector,
    norm_nonneg (WithLp.toLp 2 (fun index => vector (embedding index)))]

private theorem submatrix_applyVec (operator : HilbertOperator R)
    (embedding : S.Index → R.Index) (vector : HilbertVector S) :
    HilbertOperator.applyVec (R := S) (operator.submatrix embedding embedding) vector =
      WithLp.toLp 2 (fun index => operator.applyVec (extendVector embedding vector)
        (embedding index)) := by
  classical
  ext index
  simp only [HilbertOperator.applyVec_apply, Matrix.submatrix_apply,
    extendVector_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro other _
  simp

/-- Compress the same observable to an injectively embedded basis subspace. -/
def compress (embedding : S.Index → R.Index) (injective : Function.Injective embedding)
    (effect : Effect R) : Effect S where
  matrix := effect.matrix.submatrix embedding embedding
  positive := effect.positive.submatrix embedding
  contractive vector := by
    rw [submatrix_applyVec]
    exact (norm_restrictVector_le embedding injective
      (effect.matrix.applyVec (extendVector embedding vector))).trans
      ((effect.contractive (extendVector embedding vector)).trans_eq
        (norm_extendVector embedding injective vector))

@[simp] theorem compress_matrix (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (effect : Effect R) :
    (compress embedding injective effect).matrix =
      effect.matrix.submatrix embedding embedding := rfl

end

end QuantumAlg.Effect
