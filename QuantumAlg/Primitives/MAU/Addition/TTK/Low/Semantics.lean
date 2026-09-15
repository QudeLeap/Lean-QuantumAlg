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
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
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
theorem ttkLowRipple_matrix (n : Nat) : (lowRippleProgram n).matrix = lowOperator n := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨left, right⟩, rfl⟩ := (prodEquiv (m := n) (n := n)).surjective input
  have circuit := congrArg (fun state : NormalizedVector (Qubits (n + n)) => state output)
    ((ttkLowRipple_realizes_addition n).apply_encoded_ket (left, right))
  have semantic := congrArg (fun state : NormalizedVector (Qubits (n + n)) => state output)
    (lowOperator_ket n left right)
  have circuitColumn :=
    (HilbertOperator.applyVec_ket
      ((lowRippleProgram n).matrix : HilbertOperator (Qubits (encoding n).width))
      ((encoding n).encode (left, right)) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (lowOperator n : HilbertOperator (Qubits (n + n)))
      (prodEquiv (left, right)) output).symm.trans semantic
  exact circuitColumn.trans semanticColumn.symm

/-- The actual ripple gates, with all supplied operand wires explicitly retained. -/
def completeLowProgram (n : Nat) : UnitaryCircuit (Qubits (encoding n).width) :=
  .seq (lowRippleProgram n)
    (.identity (Qubits (encoding n).width) (List.range (n + n)) List.nodup_range)

/-- The complete frame adds no operation to the mathematical action. -/
theorem ttkCompleteLow_matrix (n : Nat) : (completeLowProgram n).matrix = lowOperator n := by
  have unchanged : (completeLowProgram n).matrix = (lowRippleProgram n).matrix := by
    apply Subtype.ext
    change (1 : HilbertOperator (Qubits (encoding n).width)) *
      ((lowRippleProgram n).matrix : HilbertOperator (Qubits (encoding n).width)) = _
    exact one_mul _
  exact unchanged.trans (ttkLowRipple_matrix n)

/-- The program uses exactly the two supplied words, including idle boundary wires. -/
theorem ttkCompleteLow_physical (n : Nat) :
    (completeLowProgram n).physical_idx = List.range (n + n) := by
  change (lowRippleProgram n).physical_idx ∪ List.range (n + n) = List.range (n + n)
  apply List.Subset.union_eq_right
  simpa only [two_mul] using (ttkLowRipple_interface n).2

/-- Declaring the existing complete frame emits no additional native event. -/
theorem ttkCompleteLow_eventCost (n : Nat) :
    (completeLowProgram n).eventCost = (lowRippleProgram n).eventCost := by
  simp only [completeLowProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

/-- The empty frame declaration adds zero depth to the actual gate schedule. -/
theorem ttkCompleteLow_depth (n : Nat) :
    (completeLowProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) := by
  rw [completeLowProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  change (lowRippleProgram n).evaluatedEventDepth (fun _ => 1) + 0 = _
  rw [add_zero, ttkLowRipple_serial_depth]

end

end QuantumAlg.MAU.Addition.TTK
