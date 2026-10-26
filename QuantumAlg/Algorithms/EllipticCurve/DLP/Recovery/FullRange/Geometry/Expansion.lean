/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry
import all QuantumAlg.Core.Base.Tensor.Linear

/-!
# The unchanged coherent good vector as one admissible-branch sum

The admissible subtype enumerates the same original finite support. Each
term retains the original branch amplitude and every Reference amplitude.
The identity neither conditions on a branch nor normalizes its good mass.
-/

namespace QuantumAlg.EllipticCurve.FullRange.Geometry

noncomputable section

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Enumerating precisely the original good support preserves the complete coherent source. -/
lemma goodVector_expansion (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G)
    {Reference : Register} (reference : NormalizedVector Reference) :
    goodVector width steps selected addend seed reference =
      ∑ branch : {branch // branch ∈ admissibleBranches width steps selected addend seed},
        ∑ ref : Reference.Index,
          (branchAmplitude width branch.val * reference ref) •
            (NormalizedVector.ket (R := (branchRegister width).prod Reference)
              (branch.val, ref)).vec := by
  classical
  unfold goodVector
  rw [← Finset.sum_coe_sort, HilbertVector.prodTensor_sum_left]
  apply Finset.sum_congr rfl
  intro branch _
  have expansion := congrArg
    (fun vector : HilbertVector Reference => HilbertVector.prodTensor
      (NormalizedVector.ket (R := branchRegister width) branch.val).vec vector)
    (HilbertVector.sum_amplitude_smul_ket reference.vec)
  rw [HilbertVector.prodTensor_smul_left, ← expansion, HilbertVector.prodTensor_sum_right]
  simp only [HilbertVector.prodTensor_smul_right, HilbertVector.prodTensor_ket,
    Finset.smul_sum, smul_smul]

end

end QuantumAlg.EllipticCurve.FullRange.Geometry
