/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Prefix and reverse invariants for batch inversion

The forward pass stores the product before each denominator. Starting from
one inverse of the complete product, two multiplications recover the current
denominator's inverse and the preceding product's inverse. These mathematical
identities describe paid native operations; they do not supply a runtime
inverse instruction or a free table computation.
-/

namespace QuantumAlg.ClassicalAlgorithms.Modular.BatchInverse

variable {F : Type*} [Field F]

/-- Product of the first count actual denominators, before the next entry. -/
def prefixProduct (values : Nat → F) : Nat → F
  | 0 => 1
  | count + 1 => prefixProduct values count * values count

/-- Nonzero denominators keep every stored forward prefix invertible. -/
lemma prefixProduct_ne_zero (values : Nat → F) (count : Nat)
    (nonzero : ∀ index < count, values index ≠ 0) : prefixProduct values count ≠ 0 := by
  induction count with
  | zero => exact one_ne_zero
  | succ count inductionHypothesis =>
      exact mul_ne_zero
        (inductionHypothesis (fun index before => nonzero index (Nat.lt_succ_of_lt before)))
        (nonzero count (Nat.lt_succ_self count))

/-- The literal two-multiply reverse step returns the row inverse and preceding inverse. -/
lemma reverse_step (partialProduct denominator : F)
    (partialNonzero : partialProduct ≠ 0) (denominatorNonzero : denominator ≠ 0) :
    (partialProduct * denominator)⁻¹ * partialProduct = denominator⁻¹ ∧
      (partialProduct * denominator)⁻¹ * denominator = partialProduct⁻¹ := by
  constructor <;> field_simp [partialNonzero, denominatorNonzero]

/-- A valid reverse accumulator suffices; no independent inverse is computed for this row. -/
lemma reverse_prefix_step (values : Nat → F) (count : Nat) (accumulator : F)
    (nonzero : ∀ index < count + 1, values index ≠ 0)
    (accumulatorValue : accumulator = (prefixProduct values (count + 1))⁻¹) :
    accumulator * prefixProduct values count = (values count)⁻¹ ∧
      accumulator * values count = (prefixProduct values count)⁻¹ := by
  rw [accumulatorValue]
  exact reverse_step _ _
    (prefixProduct_ne_zero values count (fun index before =>
      nonzero index (Nat.lt_succ_of_lt before))) (nonzero count (Nat.lt_succ_self count))

end QuantumAlg.ClassicalAlgorithms.Modular.BatchInverse
