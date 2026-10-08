/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Adjoint targets of addressed reversible qubit operations

The actual X, CNOT and Toffoli permutations are involutions. This mathematical
identity justifies using the same native operation when constructing inverse words.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

/-- Every addressed reversible qubit primitive has its original operator as its adjoint. -/
public theorem qubitPrimitive_operator_star {n : Nat} (primitive : QubitPrimitive n) :
    star primitive.operator = primitive.operator := by
  have same : primitive.perm.symm = primitive.perm := by
    cases primitive <;> rfl
  apply Subtype.ext
  change star ((primitive.perm⁻¹).permMatrix Complex) = (primitive.perm⁻¹).permMatrix Complex
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  change primitive.perm.permMatrix Complex = (primitive.perm⁻¹).permMatrix Complex
  exact congrArg (fun permutation : Equiv.Perm (Fin (2 ^ n)) =>
    permutation.permMatrix Complex) same.symm

end

end QuantumAlg.QubitPrimitive
