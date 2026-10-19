/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Geometry
import all QuantumAlg.Components.Gates.SingleQubit.Support
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual native Fourier head in selected-bank coordinates

The H token acts on the real selected head. The whole tail, every physical
complementary system and the arbitrary external reference retain their exact
basis coordinates. The equation is derived from the real gate application.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- Native H equals source H on the head and identity on the full physical remainder. -/
lemma nativeHadamard_bank_matrix_entry {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (row column : ctx.register.Index) {environment : OracleModel.empty.Interpretation} :
    ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (wires 0) (qubits 0)).matrix environment)
        row column =
      Gate.HOp (bankCoordinates wires qubits row).1.1
        (bankCoordinates wires qubits column).1.1 *
          (if (bankCoordinates wires qubits row).1.2 =
                (bankCoordinates wires qubits column).1.2 ∧
              (bankCoordinates wires qubits row).2 = (bankCoordinates wires qubits column).2
            then 1 else 0) := by
  classical
  have headEntry := congrArg₂ (fun left right : Fin 2 => Gate.HOp left right)
    (bankCoordinates_head_value wires qubits row).symm
    (bankCoordinates_head_value wires qubits column).symm
  have outside :
      (if ∀ index : Fin ctx.systemCount, index ≠ wires 0 → row index = column index
        then (1 : Complex) else 0) =
      (if (bankCoordinates wires qubits row).1.2 =
            (bankCoordinates wires qubits column).1.2 ∧
          (bankCoordinates wires qubits row).2 = (bankCoordinates wires qubits column).2
        then 1 else 0) := by
    exact if_congr (bankCoordinates_outside_head_iff wires qubits row column) rfl rfl
  exact (Gate.singleQubitAt_matrix_entry_outside ctx.quantumLayout .empty Gate.HOp
    (wires 0) (qubits 0) row column environment).trans (congrArg₂ (· * ·) headEntry outside)

/-- The real reference extension keeps every physical suffix and reference matrix entry. -/
lemma nativeHadamard_reference_matrix_entry {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (Reference : Register) (row column : (ctx.register.prod Reference).Index) {environment :
      OracleModel.empty.Interpretation} :
    (UnitaryOperator.prodTensor
      ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (wires 0) (qubits 0)).matrix
        environment)
      (1 : UnitaryOperator Reference)) row column =
      Gate.HOp (bankCoordinates wires qubits row.1).1.1
        (bankCoordinates wires qubits column.1).1.1 *
          (if (bankCoordinates wires qubits row.1).1.2 =
                (bankCoordinates wires qubits column.1).1.2 ∧
              (bankCoordinates wires qubits row.1).2 =
                (bankCoordinates wires qubits column.1).2 ∧ row.2 = column.2
            then 1 else 0) := by
  classical
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply, nativeHadamard_bank_matrix_entry]
  change (_ * (if _ then (1 : Complex) else 0)) *
    (if row.2 = column.2 then 1 else 0) = _
  by_cases tailSame : (bankCoordinates wires qubits row.1).1.2 =
      (bankCoordinates wires qubits column.1).1.2 <;>
    by_cases complementSame : (bankCoordinates wires qubits row.1).2 =
      (bankCoordinates wires qubits column.1).2 <;>
    by_cases referenceSame : row.2 = column.2 <;>
    simp only [tailSame, complementSame, referenceSame, and_self, false_and,
      and_false, if_true, if_false, mul_one, mul_zero]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
