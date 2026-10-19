/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Injective
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.NormSq
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.StarClosed

/-!
# Binary-octahedral finite facts

Assembly of the four kernel-checked finite facts and their exact-quaternion consequences.
-/

section

namespace QuantumAlg.QubitTwoDesign

private lemma factsSqrtTwoRat_add_self_injective {a b : SqrtTwoRat}
    (h : a + a = b + b) : a = b := by
  apply sqrtTwoEval_injective
  have h' := congrArg sqrtTwoEval h
  rw [map_add, map_add] at h'
  linarith

private lemma factsExact_add_self_injective {x y : ExactQuaternion}
    (h : x + x = y + y) : x = y := by
  apply QuaternionAlgebra.ext <;> apply factsSqrtTwoRat_add_self_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

/-- The exact list has `48` elements. -/
lemma binaryOctahedral_card : Fintype.card BinaryOctahedral = 48 := by
  decide

/-- Distinct codes represent distinct exact quaternions. -/
lemma binaryOctahedralQuaternion_injective :
    Function.Injective binaryOctahedralQuaternion := by
  intro a b hab
  apply octNumerator_injective
  apply octToExact_injective
  rw [octToExact_octNumerator, octToExact_octNumerator, hab]

lemma binaryOctahedralQuaternion_normSq (a : BinaryOctahedral) :
    Quaternion.normSq (binaryOctahedralQuaternion a) = 1 := by
  have hquad : (2 : SqrtTwoRat) ^ 2 * Quaternion.normSq (binaryOctahedralQuaternion a) = 4 := by
    rw [← Quaternion.normSq_smul, two_smul, ← octToExact_octNumerator, normSq_octToExact,
      octNumerator_normSq]
    simp
  apply sqrtTwoEval_injective
  have h4 := congrArg sqrtTwoEval hquad
  simp only [map_mul, map_pow, map_ofNat, map_one] at h4 ⊢
  norm_num at h4 ⊢
  linarith [h4]

lemma binaryOctahedralQuaternion_closed (a b : BinaryOctahedral) :
    ∃ c, binaryOctahedralQuaternion c =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b := by
  obtain ⟨c, hc⟩ := octNumerator_closed a b
  refine ⟨c, ?_⟩
  have key : (binaryOctahedralQuaternion a + binaryOctahedralQuaternion a) *
      (binaryOctahedralQuaternion b + binaryOctahedralQuaternion b) =
      (binaryOctahedralQuaternion c + binaryOctahedralQuaternion c) +
      (binaryOctahedralQuaternion c + binaryOctahedralQuaternion c) := by
    rw [← octToExact_octNumerator, ← octToExact_octNumerator, ← octToExact_octNumerator,
      ← map_mul, hc, map_add]
  -- key : (x+x)(y+y) = (z+z)+(z+z), i.e. (xy + xy) + (xy + xy) = (z+z)+(z+z)
  apply factsExact_add_self_injective
  apply factsExact_add_self_injective
  rw [← key]; noncomm_ring

lemma binaryOctahedralQuaternion_star_closed (a : BinaryOctahedral) :
    ∃ b, binaryOctahedralQuaternion b = star (binaryOctahedralQuaternion a) := by
  obtain ⟨b, hb⟩ := octNumerator_star_closed a
  refine ⟨b, ?_⟩
  apply factsExact_add_self_injective
  rw [← octToExact_octNumerator, hb, octToExact_star, octToExact_octNumerator]
  exact star_add (binaryOctahedralQuaternion a) (binaryOctahedralQuaternion a)

end QuantumAlg.QubitTwoDesign

end
