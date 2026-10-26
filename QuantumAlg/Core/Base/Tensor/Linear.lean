/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Bilinearity of the same raw product vector

Finite sums and complex scalars distribute through either subsystem. These
identities retain the complete coherent vector, with no normalization or
physical preparation premise.
-/

namespace QuantumAlg.HilbertVector

noncomputable section

open scoped BigOperators

/-- A finite coherent sum in the first factor remains the same complete product vector. -/
lemma prodTensor_sum_left {R S : Register} {Branch : Type*}
    (indices : Finset Branch) (left : Branch → HilbertVector R) (right : HilbertVector S) :
    prodTensor (∑ branch ∈ indices, left branch) right =
      ∑ branch ∈ indices, prodTensor (left branch) right := by
  apply WithLp.ofLp_injective
  funext index
  simp only [prodTensor_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_mul]

/-- A finite coherent sum in the second factor retains all of its original amplitudes. -/
lemma prodTensor_sum_right {R S : Register} {Branch : Type*}
    (indices : Finset Branch) (left : HilbertVector R) (right : Branch → HilbertVector S) :
    prodTensor left (∑ branch ∈ indices, right branch) =
      ∑ branch ∈ indices, prodTensor left (right branch) := by
  apply WithLp.ofLp_injective
  funext index
  simp only [prodTensor_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]

/-- A complex coefficient on the first subsystem multiplies the complete raw product. -/
lemma prodTensor_smul_left {R S : Register} (scalar : ℂ)
    (left : HilbertVector R) (right : HilbertVector S) :
    prodTensor (scalar • left) right = scalar • prodTensor left right := by
  apply WithLp.ofLp_injective
  funext index
  change (scalar * left index.1) * right index.2 = scalar * (left index.1 * right index.2)
  exact mul_assoc _ _ _

/-- A complex coefficient on the second subsystem has the same whole-vector meaning. -/
lemma prodTensor_smul_right {R S : Register} (scalar : ℂ)
    (left : HilbertVector R) (right : HilbertVector S) :
    prodTensor left (scalar • right) = scalar • prodTensor left right := by
  apply WithLp.ofLp_injective
  funext index
  change left index.1 * (scalar * right index.2) = scalar * (left index.1 * right index.2)
  ring

end

end QuantumAlg.HilbertVector
