/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Program
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.FinCases

/-!
# Full operator equality for the elementary controlled register swap

The literal Toffoli program implements controlled exchange on the original
control and two supplied words. Full matrix equality includes arbitrary
superpositions and external correlations [BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.EncodedRegisterSwap

noncomputable section

private theorem encoded_pair (width : Nat) (controlValue : Fin (2 ^ 1))
    (left right : Fin (2 ^ width)) :
    (encoding width).encode (finTwoEquiv controlValue, (left, right)) =
      prodEquiv (controlValue, prodEquiv (left, right)) := by
  fin_cases controlValue <;> rfl

/-- Actual native action on every physical control and pair of source labels. -/
theorem program_applyVec_pair (width : Nat) (controlValue : Fin (2 ^ 1))
    (left right : Fin (2 ^ width)) :
    (program width).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (controlValue, prodEquiv (left, right)))).vec =
      (NormalizedVector.ket (R := Qubits (1 + (width + width)))
        (prodEquiv (controlValue,
          if controlValue = 1 then prodEquiv (right, left)
            else prodEquiv (left, right)))).vec := by
  have actual := congrArg NormalizedVector.vec
    ((program_realizes width).apply_encoded_ket (finTwoEquiv controlValue, (left, right)))
  fin_cases controlValue
  · change (program width).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (0, prodEquiv (left, right)))).vec =
      (NormalizedVector.ket (R := Qubits (1 + (width + width)))
        (prodEquiv (0, prodEquiv (left, right)))).vec at actual
    change (program width).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv (left, right)))).vec =
      (NormalizedVector.ket (R := Qubits (1 + (width + width)))
        (prodEquiv ((0 : Fin (2 ^ 1)), if (0 : Fin (2 ^ 1)) = 1 then
          prodEquiv (right, left) else prodEquiv (left, right)))).vec
    rw [if_neg (by decide)]
    exact actual
  · change (program width).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (1, prodEquiv (left, right)))).vec =
      (NormalizedVector.ket (R := Qubits (1 + (width + width)))
        (prodEquiv (1, prodEquiv (right, left)))).vec at actual
    change (program width).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((1 : Fin (2 ^ 1)), prodEquiv (left, right)))).vec =
      (NormalizedVector.ket (R := Qubits (1 + (width + width)))
        (prodEquiv ((1 : Fin (2 ^ 1)), if (1 : Fin (2 ^ 1)) = 1 then
          prodEquiv (right, left) else prodEquiv (left, right)))).vec
    rw [if_pos rfl]
    exact actual

private theorem swap_ket (width : Nat) (left right : Fin (2 ^ width)) :
    (swapRegistersOp width).applyVec
        (NormalizedVector.ket (R := Qubits (width + width)) (prodEquiv (left, right))).vec =
      (NormalizedVector.ket (R := Qubits (width + width)) (prodEquiv (right, left))).vec := by
  rw [swapRegistersOp, UnitaryOperator.ofPerm_applyVec_ket]
  have swapped : (swapRegistersPerm width)⁻¹ (prodEquiv (left, right)) =
      prodEquiv (right, left) := by
    simp [swapRegistersPerm, Equiv.Perm.inv_def]
  rw [swapped]

/-- The complete native matrix is the independently specified controlled register exchange. -/
theorem program_matrix (width : Nat) :
    (program width).matrix = UnitaryOperator.controlledQubits (swapRegistersOp width) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨controlValue, word⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := width + width)).surjective column
  obtain ⟨⟨left, right⟩, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective word
  have expected :
      (UnitaryOperator.controlledQubits (swapRegistersOp width)).applyVec
          (NormalizedVector.ket (R := Qubits (1 + (width + width)))
            (prodEquiv (controlValue, prodEquiv (left, right)))).vec =
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (controlValue,
            if controlValue = 1 then prodEquiv (right, left)
            else prodEquiv (left, right)))).vec := by
    fin_cases controlValue
    · change (UnitaryOperator.controlledQubits (swapRegistersOp width)).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv (left, right)))).vec =
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((0 : Fin (2 ^ 1)), if (0 : Fin (2 ^ 1)) = 1 then
            prodEquiv (right, left) else prodEquiv (left, right)))).vec
      rw [if_neg (by decide)]
      have bridge : HilbertVector.tensor NormalizedVector.ket0.vec
          (NormalizedVector.ket (R := Qubits (width + width)) (prodEquiv (left, right))).vec =
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (0, prodEquiv (left, right)))).vec :=
        congrArg NormalizedVector.vec
          (NormalizedVector.tensor_ket (m := 1) (n := width + width)
            0 (prodEquiv (left, right)))
      exact (congrArg (UnitaryOperator.controlledQubits (swapRegistersOp width)).applyVec
        bridge.symm).trans
          ((UnitaryOperator.controlledQubits_applyVec_ket0_tensor _ _).trans bridge)
    · change (UnitaryOperator.controlledQubits (swapRegistersOp width)).applyVec
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((1 : Fin (2 ^ 1)), prodEquiv (left, right)))).vec =
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv ((1 : Fin (2 ^ 1)), if (1 : Fin (2 ^ 1)) = 1 then
            prodEquiv (right, left) else prodEquiv (left, right)))).vec
      rw [if_pos rfl]
      have bridge : HilbertVector.tensor NormalizedVector.ket1.vec
          (NormalizedVector.ket (R := Qubits (width + width)) (prodEquiv (left, right))).vec =
        (NormalizedVector.ket (R := Qubits (1 + (width + width)))
          (prodEquiv (1, prodEquiv (left, right)))).vec :=
        congrArg NormalizedVector.vec
          (NormalizedVector.tensor_ket (m := 1) (n := width + width)
            1 (prodEquiv (left, right)))
      exact (congrArg (UnitaryOperator.controlledQubits (swapRegistersOp width)).applyVec
        bridge.symm).trans
          ((UnitaryOperator.controlledQubits_applyVec_ket1_tensor _ _).trans
            ((congrArg (HilbertVector.tensor NormalizedVector.ket1.vec)
              (swap_ket width left right)).trans
              (congrArg NormalizedVector.vec
                (NormalizedVector.tensor_ket (m := 1) (n := width + width)
                  1 (prodEquiv (right, left))))))
  have action := (program_applyVec_pair width controlValue left right).trans expected.symm
  simpa only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    using congrArg (fun state : HilbertVector (Qubits (1 + (width + width))) => state row) action

end

end QuantumAlg.EncodedRegisterSwap
