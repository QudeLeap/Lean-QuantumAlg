/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.BranchSupport
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Coherent reference framing for prepared exponent branches

An arbitrary reference vector is retained as a tensor factor throughout the
actual preparation and its finite good-branch decomposition. Norms factor
exactly, including unnormalized good and exceptional components.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

variable {R Reference : Register}

/-- A raw vector retains the entire reference factor, including its complex phases. -/
def referenceFrame (vector : HilbertVector R) (reference : HilbertVector Reference) :
    HilbertVector (Register.prod R Reference) :=
  WithLp.toLp 2 (fun label => vector label.1 * reference label.2)

@[simp] theorem referenceFrame_apply (vector : HilbertVector R)
    (reference : HilbertVector Reference) (label : (Register.prod R Reference).Index) :
    referenceFrame vector reference label = vector label.1 * reference label.2 := rfl

/-- The full finite reference factor has its exact multiplicative norm. -/
theorem referenceFrame_norm (vector : HilbertVector R) (reference : HilbertVector Reference) :
    ‖referenceFrame vector reference‖ = ‖vector‖ * ‖reference‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  change (∑ label : R.Index × Reference.Index,
    ‖vector label.1 * reference label.2‖ ^ 2) =
      (∑ label : R.Index, ‖vector label‖ ^ 2) *
        ∑ label : Reference.Index, ‖reference label‖ ^ 2
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [norm_mul, mul_pow]

/-- Tensoring with a normalized reference state preserves normalization. -/
def normalizedReferenceFrame (vector : NormalizedVector R)
    (reference : NormalizedVector Reference) : NormalizedVector (Register.prod R Reference) :=
  NormalizedVector.ofVector (referenceFrame vector.vec reference.vec) (by
    rw [referenceFrame_norm, vector.norm_eq_one, reference.norm_eq_one, one_mul])

/-- The exact actual tensor operator retains an arbitrary coherent reference vector. -/
theorem referenceFrame_unitary (operator : UnitaryOperator R) (vector : HilbertVector R)
    (reference : HilbertVector Reference) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)).applyVec
        (referenceFrame vector reference) =
      referenceFrame (operator.applyVec vector) reference := by
  classical
  apply WithLp.ofLp_injective
  funext row
  change (∑ column : R.Index × Reference.Index,
    operator row.1 column.1 * (1 : Matrix Reference.Index Reference.Index ℂ) row.2 column.2 *
      (vector column.1 * reference column.2)) =
    (∑ column : R.Index, operator row.1 column * vector column) * reference row.2
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro column _
  simp [Matrix.one_apply, mul_assoc]

/-- Coherent subtraction retains exactly the same reference state. -/
theorem referenceFrame_sub (left right : HilbertVector R)
    (reference : HilbertVector Reference) :
    referenceFrame (left - right) reference =
      referenceFrame left reference - referenceFrame right reference := by
  apply WithLp.ofLp_injective
  funext label
  exact sub_mul _ _ _

/-- Every coordinate of the reference-framed good component comes from the original vector. -/
theorem referenceFrame_zero (vector : HilbertVector R) (reference : HilbertVector Reference)
    (label : (Register.prod R Reference).Index) (zero : vector label.1 = 0) :
    referenceFrame vector reference label = 0 := by
  rw [referenceFrame_apply, zero, zero_mul]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
