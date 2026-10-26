/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.FinCases

/-!
# Mathematical uniform preparation on selected source coordinates

These metadata-free unitaries act only on the mathematical source used to
observe the real sampler. They are not Circuit syntax or an allocated
physical bank. The symbolic count recursion supplies uniform zero columns;
selected-block transport retains every other mathematical source coordinate.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

/-- A mathematical tensor of H operators, without physical placement or resource assertions. -/
def uniformPreparation : (count : Nat) → UnitaryOperator (Qubits count)
  | 0 => 1
  | count + 1 => UnitaryOperator.reindex (prodEquiv (m := count) (n := 1))
      (UnitaryOperator.prodTensor (uniformPreparation count) Gate.HOp)

/-- All source amplitudes of the prepared zero label have their exact normalization. -/
lemma window_source_uniformPreparation_zero_column (count : Nat)
    (row : (Qubits count).Index) :
    uniformPreparation count row 0 = invSqrt2 ^ count := by
  induction count with
  | zero =>
      have same : row = (0 : Fin 1) := Fin.fin_one_eq_zero row
      subst row
      rfl
  | succ count ih =>
      have zeroSplit : (prodEquiv (m := count) (n := 1)).symm 0 = (0, 0) := by
        apply Prod.ext
        · apply Fin.ext
          simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]
        · apply Fin.ext
          simp only [prodEquiv_symm_snd_val, Fin.val_zero, Nat.zero_mod]
      change uniformPreparation count ((prodEquiv (m := count) (n := 1)).symm row).1
          ((prodEquiv (m := count) (n := 1)).symm 0).1 *
        Gate.HOp ((prodEquiv (m := count) (n := 1)).symm row).2
          ((prodEquiv (m := count) (n := 1)).symm 0).2 = _
      rw [zeroSplit, ih]
      have head (bit : Fin 2) : Gate.HOp bit 0 = invSqrt2 := by
        fin_cases bit <;> simp [Gate.HOp, UnitaryOperator.coe_ofMatrix]
      rw [head, pow_succ]

/-- Prepare one selected mathematical block and retain the entire remaining source. -/
def selectedUniformPreparation {S Rest : Register} {active : Nat}
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) : UnitaryOperator S :=
  UnitaryOperator.reindex partition.symm
    (UnitaryOperator.prodTensor (uniformPreparation active) (1 : UnitaryOperator Rest))

/-- Exact selected-block entries include identity on every other mathematical source coordinate. -/
lemma window_source_selectedPreparation_entry {S Rest : Register} {active : Nat}
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (row column : S.Index) :
    selectedUniformPreparation partition row column =
      uniformPreparation active (partition row).1 (partition column).1 *
        (if (partition row).2 = (partition column).2 then (1 : Complex) else 0) := rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
