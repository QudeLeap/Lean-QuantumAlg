/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Label
import all QuantumAlg.Components.Gates.Swap.Label
import all QuantumAlg.Components.Gates.Swap.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.BinaryLabelEncoding
public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Original addressed SWAP in ordered binary coordinates

The original integer-label permutation exchanges the two selected coordinates
of the physical basis and preserves every other coordinate.
-/

namespace QuantumAlg

noncomputable section

private lemma encoded_bit {width : Nat} (basis : Fin width → Fin 2)
    (index : Fin width) :
    (QuantumSignature.qubitsIndexEquiv width basis).val.testBit
      (WireAddress.bitIndex index).val = finTwoEquiv (basis index) := by
  change (BinaryBasis.bigEndianEquiv width basis).val.testBit
    (WireAddress.bitIndex index).val = finTwoEquiv (basis index)
  have reversed : (WireAddress.bitIndex index).val = index.rev.val := by
    simp only [WireAddress.bitIndex, Fin.val_rev]
    omega
  rw [reversed]
  exact BinaryBasis.bigEndianEquiv_bit width basis index

private lemma decoded_bit {width : Nat} (label : Fin (2 ^ width))
    (index : Fin width) :
    finTwoEquiv ((QuantumSignature.qubitsIndexEquiv width).symm label index) =
      label.val.testBit (WireAddress.bitIndex index).val := by
  have inverse := (QuantumSignature.qubitsIndexEquiv width).apply_symm_apply label
  exact (encoded_bit (width := width)
    ((QuantumSignature.qubitsIndexEquiv width).symm label) index).symm.trans
      (congrArg (fun value : Fin (2 ^ width) =>
        value.val.testBit (WireAddress.bitIndex index).val) inverse)

/-- The unchanged integer-label action exchanges exactly the two physical coordinates. -/
public lemma qftSwapLabel_coordinates {width : Nat} (left right : Fin width)
    (distinct : left ≠ right) (basis : Fin width → Fin 2) (index : Fin width) :
    (QuantumSignature.qubitsIndexEquiv width).symm
      (qftSwapLabel left right (QuantumSignature.qubitsIndexEquiv width basis)) index =
        basis (Equiv.swap left right index) := by
  apply finTwoEquiv.injective
  rw [decoded_bit]
  by_cases atLeft : index = left
  · subst index
    rw [qftSwapLabel_left left right distinct, encoded_bit, Equiv.swap_apply_left]
  · by_cases atRight : index = right
    · subst index
      rw [qftSwapLabel_right left right distinct, encoded_bit, Equiv.swap_apply_right]
    · rw [qftSwapLabel_of_ne left right index distinct atLeft atRight, encoded_bit,
        Equiv.swap_apply_of_ne_of_ne atLeft atRight]

/-- Every matrix entry of the original target is the same exact coordinate exchange. -/
public lemma qftSwapOperator_coordinates_entry {width : Nat} (left right : Fin width)
    (distinct : left ≠ right) (row column : Fin width → Fin 2) :
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
      (qftSwapOperator left right distinct) row column =
        if (fun index => row (Equiv.swap left right index)) = column then 1 else 0 := by
  change qftSwapOperator left right distinct
    (QuantumSignature.qubitsIndexEquiv width row)
    (QuantumSignature.qubitsIndexEquiv width column) = _
  change (((UnitaryOperator.ofPerm (QubitPrimitive.cnot left right distinct).perm.symm :
      UnitaryOperator (Qubits width)) *
        UnitaryOperator.ofPerm (QubitPrimitive.cnot right left distinct.symm).perm.symm) *
          UnitaryOperator.ofPerm (QubitPrimitive.cnot left right distinct).perm.symm :
            UnitaryOperator (Qubits width))
    (QuantumSignature.qubitsIndexEquiv width row)
    (QuantumSignature.qubitsIndexEquiv width column) = _
  rw [UnitaryOperator.ofPerm_mul, UnitaryOperator.ofPerm_mul, UnitaryOperator.ofPerm_entry]
  change (if qftSwapLabel left right (QuantumSignature.qubitsIndexEquiv width row) =
      QuantumSignature.qubitsIndexEquiv width column then 1 else 0) = _
  have decoded : (QuantumSignature.qubitsIndexEquiv width).symm
      (qftSwapLabel left right (QuantumSignature.qubitsIndexEquiv width row)) =
        fun index => row (Equiv.swap left right index) :=
    funext (qftSwapLabel_coordinates left right distinct row)
  have matching : qftSwapLabel left right (QuantumSignature.qubitsIndexEquiv width row) =
      QuantumSignature.qubitsIndexEquiv width column ↔
        (fun index => row (Equiv.swap left right index)) = column := by
    constructor
    · intro same
      exact (decoded.symm.trans
        (congrArg (QuantumSignature.qubitsIndexEquiv width).symm same)).trans
          ((QuantumSignature.qubitsIndexEquiv width).symm_apply_apply column)
    · intro same
      apply (QuantumSignature.qubitsIndexEquiv width).symm.injective
      exact decoded.trans
        (same.trans ((QuantumSignature.qubitsIndexEquiv width).symm_apply_apply column).symm)
  exact if_congr matching rfl rfl

end

end QuantumAlg
