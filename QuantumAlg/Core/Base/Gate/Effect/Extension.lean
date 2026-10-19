/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Basic
import all QuantumAlg.Core.Base.Gate.Effect.Embedding
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Effects extended by zero outside an injective basis subspace

An injective placement sends each original basis vector to its named target
basis vector. The extended observable acts by the same matrix on that image
and by zero on its orthogonal complement. Positivity follows from the actual
matrix sandwich, and vector contraction follows from restriction, the original
effect, and the isometric placement. The coherent density weight is exact,
including subnormalized and zero vectors. No executable gate is introduced.
-/

namespace QuantumAlg.Effect

noncomputable section

open scoped ComplexOrder

variable {R S : Register}

/-- Place every amplitude at its named basis coordinate and put zero elsewhere. -/
public def extensionVector (embedding : S.Index → R.Index) (vector : HilbertVector S) :
    HilbertVector R :=
  ∑ index, vector index • (NormalizedVector.ket (embedding index) : HilbertVector R)

/-- The finite amplitude expression retains the actual named basis labels. -/
lemma extensionVector_apply (embedding : S.Index → R.Index) (vector : HilbertVector S)
    (output : R.Index) :
    extensionVector embedding vector output =
      ∑ index, if embedding index = output then vector index else 0 := by
  classical
  simp [extensionVector, NormalizedVector.ket_apply, mul_ite, eq_comm]

/-- Injectivity recovers every source amplitude at its corresponding image coordinate. -/
lemma extensionVector_image (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (vector : HilbertVector S) (index : S.Index) :
    extensionVector embedding vector (embedding index) = vector index := by
  classical
  simp [extensionVector_apply, injective.eq_iff]

/-- Injective basis extension preserves the complete vector norm. -/
lemma norm_extensionVector (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (vector : HilbertVector S) :
    ‖extensionVector embedding vector‖ = ‖vector‖ :=
  norm_extendVector embedding injective vector

/-- The same extension preserves all complex inner products and coherent cross terms. -/
lemma extensionVector_inner (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (left right : HilbertVector S) :
    inner ℂ (extensionVector embedding left) (extensionVector embedding right) =
      inner ℂ left right := by
  classical
  let basis : S.Index → HilbertVector R := fun index => NormalizedVector.ket (embedding index)
  have orthonormal : Orthonormal ℂ basis := by
    change Orthonormal ℂ (fun index =>
      PiLp.single (β := fun _ : R.Index => ℂ) 2 (embedding index) (1 : ℂ))
    exact (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := R.Index)).comp embedding injective
  have result := orthonormal.inner_sum (fun index => left index) (fun index => right index)
    Finset.univ
  simpa only [extensionVector, basis, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, mul_comm] using result

private def extensionMatrix (embedding : S.Index → R.Index) : Matrix R.Index S.Index ℂ :=
  fun row column => if embedding column = row then 1 else 0

private lemma extensionMatrix_mulVec (embedding : S.Index → R.Index)
    (vector : HilbertVector S) :
    (extensionMatrix embedding).mulVec vector.ofLp =
      (extensionVector embedding vector).ofLp := by
  classical
  funext row
  simp only [Matrix.mulVec, dotProduct, extensionMatrix, extensionVector_apply,
    ite_mul, one_mul, zero_mul]

private lemma extensionMatrix_conjTranspose_mulVec (embedding : S.Index → R.Index)
    (vector : HilbertVector R) :
    (extensionMatrix embedding).conjTranspose.mulVec vector.ofLp =
      fun index => vector (embedding index) := by
  classical
  funext index
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, extensionMatrix]

private lemma extension_applyVec (embedding : S.Index → R.Index)
    (operator : HilbertOperator S) (vector : HilbertVector R) :
    HilbertOperator.applyVec
        (extensionMatrix embedding * operator * (extensionMatrix embedding).conjTranspose)
        vector =
      extensionVector embedding
        (operator.applyVec (WithLp.toLp 2 (fun index => vector (embedding index)))) := by
  unfold HilbertOperator.applyVec
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    extensionMatrix_conjTranspose_mulVec]
  change WithLp.toLp 2 ((extensionMatrix embedding).mulVec
    (operator.applyVec (WithLp.toLp 2 (fun index => vector (embedding index)))).ofLp) = _
  rw [extensionMatrix_mulVec]
  rfl

/-- Extend the same positive contraction by zero off its injectively placed basis subspace. -/
def extend (embedding : S.Index → R.Index) (injective : Function.Injective embedding)
    (effect : Effect S) : Effect R where
  matrix := extensionMatrix embedding * effect.matrix * (extensionMatrix embedding).conjTranspose
  positive := effect.positive.mul_mul_conjTranspose_same (extensionMatrix embedding)
  contractive vector := by
    rw [extension_applyVec, norm_extensionVector embedding injective]
    exact (effect.contractive _).trans (norm_restrictVector_le embedding injective vector)

/-- Each pair of image coordinates retains exactly its original matrix entry. -/
lemma extend_matrix_image (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (effect : Effect S) (left right : S.Index) :
    (extend embedding injective effect).matrix (embedding left) (embedding right) =
      effect.matrix left right := by
  classical
  simp [extend, Matrix.mul_apply, Matrix.conjTranspose_apply, extensionMatrix,
    injective.eq_iff]

/-- Every matrix entry with a coordinate outside the selected subspace is zero. -/
lemma extend_matrix_eq_zero (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (effect : Effect S) (left right : R.Index)
    (outside : left ∉ Set.range embedding ∨ right ∉ Set.range embedding) :
    (extend embedding injective effect).matrix left right = 0 := by
  classical
  rcases outside with leftOutside | rightOutside
  · have different : ∀ index, embedding index ≠ left :=
      fun index same => leftOutside ⟨index, same⟩
    simp [extend, Matrix.mul_apply, extensionMatrix, different]
  · have different : ∀ index, embedding index ≠ right :=
      fun index same => rightOutside ⟨index, same⟩
    simp [extend, Matrix.mul_apply, Matrix.conjTranspose_apply, extensionMatrix, different]

/-- Applying the extended effect restricts to its source, acts there, and embeds the result. -/
lemma extend_applyVec (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (effect : Effect S) (vector : HilbertVector R) :
    (extend embedding injective effect).matrix.applyVec vector =
      extensionVector embedding
        (effect.matrix.applyVec (WithLp.toLp 2 (fun index => vector (embedding index)))) :=
  extension_applyVec embedding effect.matrix vector

/-- A whole coherent subnormalized input has precisely its original observable weight. -/
lemma extend_weight_ofSubnormalizedVector (embedding : S.Index → R.Index)
    (injective : Function.Injective embedding) (effect : Effect S)
    (vector : HilbertVector S) (bounded : ‖vector‖ ≤ 1) :
    (extend embedding injective effect).weight
        (DensityOperator.ofSubnormalizedVector (extensionVector embedding vector)
          (by rw [norm_extensionVector embedding injective]; exact bounded)) =
      effect.weight (DensityOperator.ofSubnormalizedVector vector bounded) := by
  rw [weight_ofSubnormalizedVector, weight_ofSubnormalizedVector]
  unfold HilbertOperator.quadraticWeight
  rw [extend_applyVec]
  have restricted : WithLp.toLp 2
      (fun index => extensionVector embedding vector (embedding index)) = vector := by
    ext index
    exact extensionVector_image embedding injective vector index
  rw [restricted, extensionVector_inner embedding injective]

end

end QuantumAlg.Effect
