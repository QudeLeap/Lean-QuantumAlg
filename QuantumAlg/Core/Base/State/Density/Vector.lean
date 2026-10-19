/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density

/-!
# Coherent subnormalized vectors as density operators

A projected coherent input need not have norm one. Its rank-one density keeps
the original squared norm as probability mass, including the zero vector.
This is the same outer-product convention as the normalized pure embedding.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

open scoped ComplexOrder

variable {R : Register}

private lemma trace_vectorOuterProduct (vector : HilbertVector R) :
    (Matrix.vecMulVec (fun index => vector index) (fun index => star (vector index))).trace.re =
      ‖vector‖ ^ 2 := by
  have innerEquality :
      (Matrix.vecMulVec (fun index => vector index)
        (fun index => star (vector index))).trace = inner ℂ vector vector := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
      PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  rw [innerEquality, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A coherent vector of norm at most one retains its exact subnormalized rank-one density. -/
def ofSubnormalizedVector (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1) :
    DensityOperator R where
  matrix := Matrix.vecMulVec (fun index => vector index) (fun index => star (vector index))
  positive := Matrix.posSemidef_vecMulVec_self_star (fun index => vector index)
  trace_le_one := by
    rw [trace_vectorOuterProduct]
    nlinarith [norm_nonneg vector]

@[simp] lemma ofSubnormalizedVector_matrix (vector : HilbertVector R)
    (bounded : ‖vector‖ ≤ 1) (row column : R.Index) :
    (ofSubnormalizedVector vector bounded).matrix row column =
      vector row * star (vector column) := rfl

/-- No branch normalization is performed: the mass is precisely the squared vector norm. -/
lemma ofSubnormalizedVector_mass (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1) :
    (ofSubnormalizedVector vector bounded).mass = ‖vector‖ ^ 2 :=
  trace_vectorOuterProduct vector

/-- On normalized vectors, the same construction agrees with the canonical pure embedding. -/
lemma ofSubnormalizedVector_of_normalized (vector : NormalizedVector R) :
    ofSubnormalizedVector (R := R) (vector : HilbertVector R)
      (by rw [vector.norm_eq_one]) = ofPure vector := by
  apply ext
  rfl

/-- A coherent support condition gives the diagonal support used by exact density execution. -/
lemma ofSubnormalizedVector_supported (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1)
    (allowed : R.Index → Prop) (support : ∀ index, ¬allowed index → vector index = 0) :
    ∀ index, ¬allowed index → (ofSubnormalizedVector vector bounded).matrix index index = 0 := by
  intro index outside
  rw [ofSubnormalizedVector_matrix, support index outside, zero_mul]

end

end QuantumAlg.DensityOperator
