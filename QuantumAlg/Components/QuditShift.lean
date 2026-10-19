/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Unitary
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic shifts on one finite-dimensional physical system

The mathematical shift adds a fixed finite value at one selected wire of a
heterogeneous quantum layout. Every other basis coordinate is unchanged.
This operator does not declare a native gate. Execution requires an actual
realization in the selected gate and oracle model.

The operator is certified by its computational-basis permutation. Its use in
state evolution follows unitary conjugation [dW19, qcnotes.tex:5405].
-/

section

namespace QuantumAlg.QuditShift

noncomputable section

variable {systemCount : Nat}

private instance positiveDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private def labelShift (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : Equiv.Perm layout.Basis where
  toFun basis := Function.update basis wire (basis wire + amount)
  invFun basis := Function.update basis wire (basis wire - amount)
  left_inv basis := by
    funext index
    by_cases same : index = wire
    · subst index
      simp
    · simp [Function.update_of_ne same]
  right_inv basis := by
    funext index
    by_cases same : index = wire
    · subst index
      simp
    · simp [Function.update_of_ne same]

/-- Add the shift amount modulo the selected physical system's dimension. -/
public def operator (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : UnitaryOperator layout.register :=
  UnitaryOperator.ofPerm (R := layout.register) (labelShift layout wire amount).symm

/-- Exact basis action on the complete heterogeneous register. -/
lemma operator_apply_ket (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (operator layout wire amount).apply (NormalizedVector.ket basis) =
      NormalizedVector.ket (R := layout.register)
        (Function.update basis wire (basis wire + amount)) := by
  exact UnitaryOperator.ofPerm_apply_ket (R := layout.register)
    (labelShift layout wire amount).symm basis

/-- Public basis action of the finite-dimensional shift operator. -/
public lemma quditShift_operator_apply_ket (layout : QuantumLayout systemCount)
    (wire : Fin systemCount) (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (operator layout wire amount).apply (NormalizedVector.ket basis) =
      NormalizedVector.ket (R := layout.register)
        (Function.update basis wire (basis wire + amount)) :=
  operator_apply_ket layout wire amount basis

/-- The selected wire is updated by addition in its own finite basis. -/
lemma shifted_selected_value (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (Function.update basis wire (basis wire + amount)) wire = basis wire + amount := by
  simp

/-- Every unselected physical system keeps its original basis value,
independently of its dimension. -/
lemma shifted_other_value (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis)
    (other : Fin systemCount) (different : other ≠ wire) :
    (Function.update basis wire (basis wire + amount)) other = basis other := by
  simp [Function.update_of_ne different]


end

end QuantumAlg.QuditShift

end
