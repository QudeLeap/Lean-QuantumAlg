/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts

/-!
# Binary-octahedral group structure

The finite exact-quaternion facts induce the strict binary-octahedral group operations.
-/

section

namespace QuantumAlg.QubitTwoDesign

private theorem groupSqrtTwoRat_add_self_injective {a b : SqrtTwoRat}
    (h : a + a = b + b) : a = b := by
  apply sqrtTwoEval_injective
  have h' := congrArg sqrtTwoEval h
  rw [map_add, map_add] at h'
  linarith

private theorem groupExact_add_self_injective {x y : ExactQuaternion}
    (h : x + x = y + y) : x = y := by
  apply QuaternionAlgebra.ext <;> apply groupSqrtTwoRat_add_self_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

noncomputable instance instMulBinaryOctahedral : Mul BinaryOctahedral where
  mul a b := Classical.choose (binaryOctahedralQuaternion_closed a b)

instance : One BinaryOctahedral := ⟨.axis false 0⟩

noncomputable instance instInvBinaryOctahedral : Inv BinaryOctahedral where
  inv a := Classical.choose (binaryOctahedralQuaternion_star_closed a)

/-- The exact quaternion realization respects multiplication. -/
theorem binaryOctahedralQuaternion_mul (a b : BinaryOctahedral) :
    binaryOctahedralQuaternion (a * b) =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b :=
  by
    change binaryOctahedralQuaternion
      (Classical.choose (binaryOctahedralQuaternion_closed a b)) = _
    exact Classical.choose_spec (binaryOctahedralQuaternion_closed a b)

@[simp]
theorem binaryOctahedralQuaternion_one : binaryOctahedralQuaternion 1 = 1 := by
  change signed false 1 • quaternionBasis 0 = 1
  rw [show signed false (1 : SqrtTwoRat) = 1 by rfl, one_smul]
  rfl

@[simp]
theorem binaryOctahedralQuaternion_inv (a : BinaryOctahedral) :
    binaryOctahedralQuaternion a⁻¹ = star (binaryOctahedralQuaternion a) :=
  by
    change binaryOctahedralQuaternion
      (Classical.choose (binaryOctahedralQuaternion_star_closed a)) = _
    exact Classical.choose_spec (binaryOctahedralQuaternion_star_closed a)

noncomputable instance : Group BinaryOctahedral := Group.ofLeftAxioms
  (fun a b c => binaryOctahedralQuaternion_injective <| by
    simp only [binaryOctahedralQuaternion_mul, mul_assoc])
  (fun a => binaryOctahedralQuaternion_injective <| by
    simp only [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_one, one_mul])
  (fun a => binaryOctahedralQuaternion_injective <| by
    rw [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_inv,
      Quaternion.star_mul_self, binaryOctahedralQuaternion_normSq]
    exact binaryOctahedralQuaternion_one.symm)

end QuantumAlg.QubitTwoDesign

end
