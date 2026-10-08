/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.MAU.Addition.TTK.Correctness
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Independent two-word sum and the complete TTK operand frame

The mathematical operator preserves the addend and adds it into the other
word modulo its capacity. The literal ripple program equals this operator
on the full two-word register. Declaring all supplied operand wires retains
idle wires at small widths without allocating another quantum system
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

private def lowPermutation (n : Nat) : Equiv.Perm (Fin (2 ^ (n + n))) :=
  letI : NeZero (2 ^ n) := ⟨Nat.ne_of_gt (Nat.two_pow_pos n)⟩
  (prodEquiv (m := n) (n := n)).symm.trans
    ((Equiv.prodCongrRight fun left : Fin (2 ^ n) => Equiv.addLeft left).trans prodEquiv)

private theorem lowPermutation_apply (n : Nat) (left right : Fin (2 ^ n)) :
    lowPermutation n (prodEquiv (left, right)) =
      prodEquiv (left,
        (⟨(left.val + right.val) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n))) := by
  simp only [lowPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Metadata-free addition on the two complete operand words. -/
public def lowOperator (n : Nat) : UnitaryOperator (Qubits (n + n)) :=
  UnitaryOperator.ofPerm (lowPermutation n).symm

/-- Arithmetic meaning, preserving the addend and writing the low sum. -/
theorem lowOperator_ket (n : Nat) (left right : Fin (2 ^ n)) :
    (lowOperator n).apply (NormalizedVector.ket (prodEquiv (left, right))) =
      NormalizedVector.ket (R := Qubits (n + n))
        (prodEquiv (left,
          (⟨(left.val + right.val) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n)))) := by
  rw [lowOperator, UnitaryOperator.ofPerm_apply_ket]
  exact congrArg NormalizedVector.ket (lowPermutation_apply n left right)

/-- Public tensor-basis action: retain the addend and write the modular low sum. -/
public theorem lowOperator_tensorKet (n : Nat) (left right : Fin (2 ^ n)) :
    (lowOperator n).apply ((NormalizedVector.ket left).tensor (NormalizedVector.ket right)) =
      (NormalizedVector.ket left).tensor
        (NormalizedVector.ket
          (⟨(left.val + right.val) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n))) := by
  simpa only [NormalizedVector.tensor_ket] using lowOperator_ket n left right

/-- Exact operator equality of the actual ripple adder on arbitrary joint operand states. -/
theorem ttkLowRipple_matrix (n : Nat) :
    (lowRippleProgram n).binaryMatrix = lowOperator n := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨left, right⟩, rfl⟩ := (prodEquiv (m := n) (n := n)).surjective input
  have circuitAction :=
    UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      (lowRippleProgram n) ((encoding n).encode (left, right))
        ((encoding n).encode (lowOutput (left, right)))
          ((ttkLowRipple_realizes_addition n).apply_encoded_ket (left, right))
  have circuit := congrArg (fun state : NormalizedVector (Qubits (n + n)) => state output)
    circuitAction
  have semantic := congrArg (fun state : NormalizedVector (Qubits (n + n)) => state output)
    (lowOperator_ket n left right)
  have circuitColumn :=
    (HilbertOperator.applyVec_ket
      ((lowRippleProgram n).binaryMatrix : HilbertOperator (Qubits (encoding n).width))
      ((encoding n).encode (left, right)) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (lowOperator n : HilbertOperator (Qubits (n + n)))
      (prodEquiv (left, right)) output).symm.trans semantic
  exact circuitColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Addition.TTK
