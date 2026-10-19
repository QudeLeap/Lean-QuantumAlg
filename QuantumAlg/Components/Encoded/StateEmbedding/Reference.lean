/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.StateEmbedding

/-!
# Reference contraction through a faithful basis encoding

The encoding changes only the local basis. Each fixed pair of reference
indices gives an ordinary rectangular matrix sandwich, whose trace is
unchanged. This applies to every operator block, including coherent
off-diagonal reference entries and subnormalized measurement branches
[dW19, qcnotes.tex:5381-5409].
-/

namespace QuantumAlg.BasisEmbedding

noncomputable section

open scoped BigOperators Kronecker

variable {R S : Register}

/-- A reference block of the encoded operator is the same local matrix sandwich. -/
lemma reference_sandwich_block (embedding : S.Index ↪ R.Index) (Reference : Register)
    (operator : HilbertOperator (S.prod Reference))
    (left right : Reference.Index) (row column : R.Index) :
    (matrix (withReference embedding Reference) * operator *
        (matrix (withReference embedding Reference)).conjTranspose)
          (row, left) (column, right) =
      (matrix embedding *
        (Matrix.of (fun source target => operator (source, left) (target, right))) *
        (matrix embedding).conjTranspose) row column := by
  classical
  rw [reference_matrix]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite star, star_zero,
    mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine (Fintype.sum_prod_type (fun index : S.Index × Reference.Index =>
    if right = index.2 then
      (∑ source : S.Index, matrix embedding row source * operator (source, left) index) *
        star (matrix embedding column index.1) else 0)).trans ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Tracing only the encoded local system retains every original reference matrix entry. -/
lemma reference_sandwich_sum (embedding : S.Index ↪ R.Index) (Reference : Register)
    (operator : HilbertOperator (S.prod Reference)) (left right : Reference.Index) :
    (∑ basis : R.Index,
      (matrix (withReference embedding Reference) * operator *
          (matrix (withReference embedding Reference)).conjTranspose)
            (basis, left) (basis, right)) =
      ∑ basis : S.Index, operator (basis, left) (basis, right) := by
  simp_rw [reference_sandwich_block]
  exact trace_sandwich embedding (fun source target => operator (source, left) (target, right))

end

end QuantumAlg.BasisEmbedding
