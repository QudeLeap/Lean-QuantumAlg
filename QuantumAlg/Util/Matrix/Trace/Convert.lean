/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Ordered conversion factors around a finite matrix trace

Two fixed matrix factors surround every term of the same finite path sum.
The intermediate density fibers are related by their exact preparation
sandwich, without normalization or restrictions on the finite predicates.
-/

namespace QuantumAlg.MatrixTrace

noncomputable section

open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Exact preparation fibers compose with every retained finite path in its original order. -/
lemma sandwich_sum_of_prepared {Path Store Index : Type}
    [Fintype Path] [Fintype Store] [Fintype Index]
    (forward inverse : Matrix Index Index ℂ) (branch : Path → Matrix Index Index ℂ)
    (valid : Path → Store → Prop) (prepared original : Store → Matrix Index Index ℂ)
    (input : ∀ stored, prepared stored = inverse * original stored * inverse.conjTranspose) :
    forward * (∑ path : Path, ∑ stored : Store,
      if valid path stored then branch path * prepared stored * (branch path).conjTranspose
      else 0) * forward.conjTranspose =
      ∑ path : Path, ∑ stored : Store, if valid path stored then
        (forward * branch path * inverse) * original stored *
          (forward * branch path * inverse).conjTranspose else 0 := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro path _
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro stored _
  by_cases retained : valid path stored
  · rw [if_pos retained, if_pos retained, input stored]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [if_neg retained, if_neg retained, Matrix.mul_zero, Matrix.zero_mul]

end

end QuantumAlg.MatrixTrace
