/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Register.Action
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Gates.Swap.Controlled.Register.Action
import all QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Original binary labels of the complete controlled register exchange

The physical control and both word segments decode from their original labels.
The native permutation exchanges both labels only on the control-one branch,
including zero-width words. No workspace encoding is introduced.
-/

namespace QuantumAlg.Gate.ControlledRegisterSwap

noncomputable section

private def decoded (width : Nat) (value : Fin 2) (first second : Fin (2 ^ width)) :
    Fin (1 + (width + width)) → Fin 2 :=
  (QuantumSignature.qubitsIndexEquiv (1 + (width + width))).symm
    (prodEquiv (value, prodEquiv (first, second)))

private theorem decoded_control (width : Nat) (value : Fin 2)
    (first second : Fin (2 ^ width)) :
    decoded width value first second (control width) = value := by
  have actual := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := width + width) value (prodEquiv (first, second)) 0
  have single : (BinaryBasis.bigEndianEquiv 1).symm value 0 = value := by
    fin_cases value <;> rfl
  exact actual.trans single

private theorem decoded_left (width : Nat) (value : Fin 2)
    (first second : Fin (2 ^ width)) (index : Fin width) :
    decoded width value first second (left width index) =
      (QuantumSignature.qubitsIndexEquiv width).symm first index := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := width + width) value (prodEquiv (first, second))
    (Fin.castAdd width index)
  exact outer.trans (BinaryBasis.bigEndianEquiv_prod_left first second index)

private theorem decoded_right (width : Nat) (value : Fin 2)
    (first second : Fin (2 ^ width)) (index : Fin width) :
    decoded width value first second (right width index) =
      (QuantumSignature.qubitsIndexEquiv width).symm second index := by
  have position : right width index = Fin.natAdd 1 (Fin.natAdd width index) := by
    apply Fin.ext
    simp only [right, Fin.val_natAdd]
    omega
  rw [position]
  exact (BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := width + width) value (prodEquiv (first, second))
    (Fin.natAdd width index)).trans
      (BinaryBasis.bigEndianEquiv_prod_right first second index)

private theorem coordinates_ext (width : Nat) (first second : Fin (1 + (width + width)) → Fin 2)
    (sameControl : first (control width) = second (control width))
    (sameLeft : ∀ index, first (left width index) = second (left width index))
    (sameRight : ∀ index, first (right width index) = second (right width index)) :
    first = second := by
  funext position
  by_cases zero : position.val = 0
  · have same : position = control width := Fin.ext zero
    rw [same]
    exact sameControl
  · by_cases inLeft : position.val ≤ width
    · let index : Fin width := ⟨position.val - 1, by omega⟩
      have same : position = left width index := by
        apply Fin.ext
        change position.val = 1 + (position.val - 1)
        omega
      rw [same]
      exact sameLeft index
    · let index : Fin width := ⟨position.val - (1 + width), by omega⟩
      have same : position = right width index := by
        apply Fin.ext
        change position.val = 1 + width + (position.val - (1 + width))
        omega
      rw [same]
      exact sameRight index

/-- The complete native row permutation exchanges exactly the two original binary words. -/
theorem complete_decoded (width : Nat) (value : Fin 2) (first second : Fin (2 ^ width)) :
    sequencePermutation width (List.finRange width) (decoded width value first second) =
      if value = 0 then decoded width value first second else decoded width value second first := by
  have action := sequence_coordinates width (List.finRange width) (List.nodup_finRange width)
    (decoded width value first second)
  apply coordinates_ext width
  · rw [action.1, decoded_control]
    split <;> rw [decoded_control]
  · intro index
    rw [(action.2 index).1, decoded_control]
    simp only [List.mem_finRange, if_true]
    by_cases zero : value = 0
    · rw [if_pos zero, if_pos zero]
    · rw [if_neg zero, if_neg zero, decoded_right, decoded_left]
  · intro index
    rw [(action.2 index).2, decoded_control]
    simp only [List.mem_finRange, if_true]
    by_cases zero : value = 0
    · rw [if_pos zero, if_pos zero]
    · rw [if_neg zero, if_neg zero, decoded_left, decoded_right]

end

end QuantumAlg.Gate.ControlledRegisterSwap
