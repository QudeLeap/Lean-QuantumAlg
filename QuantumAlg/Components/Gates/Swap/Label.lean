/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Operator
import all QuantumAlg.Components.Gates.Swap.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Original addressed SWAP label action

The original three-CNOT operator exchanges the addressed bits and preserves
every other bit. The basis action is independent of executable circuit syntax
and resource coordinates.
-/

namespace QuantumAlg

noncomputable section

/-- Basis-label action of the usual three-CNOT addressed SWAP. -/
public def qftSwapLabel {n : Nat} (left right : Fin n)
    (label : Fin (2 ^ n)) : Fin (2 ^ n) :=
  WireAddress.cnotMap left right
    (WireAddress.cnotMap right left
      (WireAddress.cnotMap left right label))

@[simp]
lemma qftSwapLabel_left {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex left).val =
      label.val.testBit (WireAddress.bitIndex right).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne)]

@[simp]
lemma qftSwapLabel_right {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex right).val =
      label.val.testBit (WireAddress.bitIndex left).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne),
        WireAddress.bit_flipBit_of_ne hne]

@[simp]
lemma qftSwapLabel_of_ne {n : Nat} (left right bit : Fin n)
    (hne : left ≠ right) (hleft : bit ≠ left) (hright : bit ≠ right)
    (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex bit).val =
      label.val.testBit (WireAddress.bitIndex bit).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne),
        WireAddress.bit_flipBit_of_ne (Ne.symm hleft),
        WireAddress.bit_flipBit_of_ne (Ne.symm hright)]

@[simp]
public lemma qftSwapOperator_applyVec_ket {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapOperator left right hne).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftSwapLabel left right label) :
        HilbertVector (Qubits n)) := by
  change
    (((QubitPrimitive.operator (.cnot left right hne)) *
        (QubitPrimitive.operator (.cnot right left hne.symm)) *
          (QubitPrimitive.operator (.cnot left right hne))).applyVec
        (NormalizedVector.ket (R := Qubits n) label :
          HilbertVector (Qubits n))) = _
  rw [UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec]
  change
    ((((QubitPrimitive.operator (.cnot left right hne)).apply
        ((QubitPrimitive.operator (.cnot right left hne.symm)).apply
          ((QubitPrimitive.operator (.cnot left right hne)).apply
            (NormalizedVector.ket (R := Qubits n) label)))) :
        NormalizedVector (Qubits n)) : HilbertVector (Qubits n)) = _
  rw [QubitPrimitive.operator_apply_ket,
    QubitPrimitive.operator_apply_ket,
    QubitPrimitive.operator_apply_ket]
  rfl

end

end QuantumAlg
