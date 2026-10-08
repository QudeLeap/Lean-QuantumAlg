/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.Entries
public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact phase of a diagonal native gate at an original qubit position

The phase is read from the model-owned one-qubit operator. The actual placed
instruction leaves every complete computational label unchanged, including all
complementary wires, and retains the exact scalar rather than a projective state.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- A diagonal native gate has precisely its selected-wire phase on the complete interface. -/
public theorem singleQubitAt_diagonal_entry {count : Nat} (layout : QubitLayout count)
    (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1)) (phase : Fin 2 → ℂ)
    (diagonal : ∀ row column, operator row column = if row = column then phase column else 0)
    (target : Fin count) (row column : Fin count → Fin 2) :
    (singleQubitAt layout.toQuantum oracles operator target rfl).matrix row column =
      if row = column then phase (column target) else 0 := by
  classical
  let application := singleQubitApplication layout.toQuantum operator target rfl
  refine (singleQubitAt_matrix_entry layout.toQuantum oracles operator target rfl
    row column).trans ?_
  change operator (row target) (column target) *
    (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [diagonal]
  by_cases same : row = column
  · subst row
    simp
  · by_cases selected : row target = column target
    · have different : (application.basisEquiv row).2 ≠
          (application.basisEquiv column).2 := by
        intro complement
        apply same
        apply application.basisEquiv.injective
        apply Prod.ext _ complement
        funext index
        change Fin 1 at index
        fin_cases index
        apply Fin.ext
        change (row target).val = (column target).val
        exact congrArg Fin.val selected
      rw [if_pos selected, if_neg different, if_neg same, mul_zero]
    · rw [if_neg selected, if_neg same, zero_mul]

/-- The actual native instruction preserves each full ket with its exact selected-wire phase. -/
public theorem singleQubitAt_diagonal_applyVec_ket {count : Nat} (layout : QubitLayout count)
    (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1)) (phase : Fin 2 → ℂ)
    (diagonal : ∀ row column, operator row column = if row = column then phase column else 0)
    (target : Fin count) (column : Fin count → Fin 2) :
    (singleQubitAt layout.toQuantum oracles operator target rfl).matrix.applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register) column).vec =
      phase (column target) •
        (NormalizedVector.ket (R := layout.toQuantum.register) column).vec := by
  classical
  ext row
  refine (HilbertOperator.applyVec_ket (R := layout.toQuantum.register)
    (singleQubitAt layout.toQuantum oracles operator target rfl).matrix column row).trans ?_
  refine (singleQubitAt_diagonal_entry layout oracles operator phase diagonal
    target row column).trans ?_
  have observed := NormalizedVector.ket_apply (R := layout.toQuantum.register) column row
  refine Eq.trans ?_ (congrArg (fun value : ℂ => phase (column target) * value) observed).symm
  by_cases same : row = column
  · simp only [same, ite_true, mul_ite, mul_one, mul_zero]
    exact (if_pos rfl).symm
  · simp only [same, ite_false, mul_zero, ite_eq_right_iff]
    intro equal
    exact False.elim (same equal)

end

end QuantumAlg.Gate
