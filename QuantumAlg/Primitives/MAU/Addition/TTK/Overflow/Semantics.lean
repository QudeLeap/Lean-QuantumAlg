/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Logic.Equiv.Prod

import Mathlib.Logic.Equiv.Bool

/-!
# Independent sum with an explicit XOR carry output

The mathematical permutation first toggles the supplied output bit by the
carry predicate and then translates the target word. Its definition contains
no circuit. The literal TTK gates equal this operator on the complete operand
and output frame, including an arbitrary initial output bit
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

private def overflowLabelPermutation (n : Nat) : Equiv.Perm (OverflowRegisters n) :=
  letI : NeZero (2 ^ n) := ⟨Nat.ne_of_gt (Nat.two_pow_pos n)⟩
  (Equiv.prodCongrRight fun pair : Registers n =>
      if 2 ^ n ≤ pair.1.val + pair.2.val then Equiv.boolNot else Equiv.refl Bool).trans
    (Equiv.prodCongr
      (Equiv.prodCongrRight fun left : Fin (2 ^ n) => Equiv.addLeft left)
      (Equiv.refl Bool))

private theorem overflowLabelPermutation_apply (n : Nat) (state : OverflowRegisters n) :
    overflowLabelPermutation n state = overflowOutput state := by
  rcases state with ⟨⟨left, right⟩, flag⟩
  apply Prod.ext
  · rfl
  · by_cases carry : 2 ^ n ≤ left.val + right.val
    · cases flag <;> simp [overflowLabelPermutation, overflowOutput, carry]
    · cases flag <;> simp [overflowLabelPermutation, overflowOutput, carry]

private def overflowBasis (n : Nat) : OverflowRegisters n ≃ Fin (2 ^ (n + n + 1)) :=
  (Equiv.prodCongr (prodEquiv (m := n) (n := n)) finTwoEquiv.symm).trans
    (prodEquiv (m := n + n) (n := 1))

private theorem overflowBasis_encode (n : Nat) (state : OverflowRegisters n) :
    overflowBasis n state = (overflowEncoding n).encode state := by
  rcases state with ⟨⟨left, right⟩, flag⟩
  cases flag <;> rfl

private def overflowPermutation (n : Nat) : Equiv.Perm (Fin (2 ^ (n + n + 1))) :=
  (overflowBasis n).symm.trans ((overflowLabelPermutation n).trans (overflowBasis n))

/-- Metadata-free addition with a supplied arbitrary XOR carry-output bit. -/
public def overflowOperator (n : Nat) : UnitaryOperator (Qubits (n + n + 1)) :=
  UnitaryOperator.ofPerm (overflowPermutation n).symm

private theorem overflowOperator_ket (n : Nat) (state : OverflowRegisters n) :
    (overflowOperator n).apply (NormalizedVector.ket ((overflowEncoding n).encode state)) =
      NormalizedVector.ket ((overflowEncoding n).encode (overflowOutput state)) := by
  have action := UnitaryOperator.ofPerm_apply_ket
    (R := Qubits (n + n + 1)) (overflowPermutation n).symm
    ((overflowEncoding n).encode state)
  refine action.trans (congrArg NormalizedVector.ket ?_)
  have decoded : (overflowBasis n).symm ((overflowEncoding n).encode state) = state :=
    (congrArg (overflowBasis n).symm (overflowBasis_encode n state).symm).trans
      ((overflowBasis n).symm_apply_apply state)
  exact (congrArg ((overflowBasis n) ∘ (overflowLabelPermutation n)) decoded).trans
    ((congrArg (overflowBasis n) (overflowLabelPermutation_apply n state)).trans
      (overflowBasis_encode n (overflowOutput state)))

/-- Public basis action retains the addend and xors the carry into either initial bit. -/
public theorem overflowOperator_tensorKet (n : Nat) (left right : Fin (2 ^ n))
    (flag : Bool) :
    (overflowOperator n).apply
      (((NormalizedVector.ket left).tensor (NormalizedVector.ket right)).tensor
        (NormalizedVector.ket (if flag then (1 : Fin 2) else 0))) =
      (((NormalizedVector.ket left).tensor
        (NormalizedVector.ket
          (⟨(left.val + right.val) % 2 ^ n,
            Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n)))).tensor
        (NormalizedVector.ket
          (if flag ^^ decide (2 ^ n ≤ left.val + right.val)
            then (1 : Fin 2) else 0))) := by
  simp only [NormalizedVector.tensor_ket]
  have action := overflowOperator_ket n ((left, right), flag)
  change (overflowOperator n).apply
      (NormalizedVector.ket
        (prodEquiv (prodEquiv (left, right), if flag then (1 : Fin 2) else 0))) =
    NormalizedVector.ket
      (prodEquiv
        (prodEquiv (left,
          (⟨(left.val + right.val) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n))),
        if flag ^^ decide (2 ^ n ≤ left.val + right.val) then (1 : Fin 2) else 0)) at action
  exact action

/-- The actual TTK overflow program equals the independent arithmetic operator. -/
theorem ttkOverflow_matrix (n : Nat) : (overflowProgram n).matrix = overflowOperator n := by
  apply Subtype.ext
  ext output input
  obtain ⟨state, rfl⟩ := (overflowBasis n).surjective input
  rw [overflowBasis_encode]
  have circuit := congrArg (fun state : NormalizedVector (Qubits (n + n + 1)) => state output)
    ((ttkOverflow_realizes_addition n).apply_encoded_ket state)
  have semantic := congrArg (fun state : NormalizedVector (Qubits (n + n + 1)) => state output)
    (overflowOperator_ket n state)
  have circuitColumn :=
    (HilbertOperator.applyVec_ket
      ((overflowProgram n).matrix : HilbertOperator (Qubits (overflowEncoding n).width))
      ((overflowEncoding n).encode state) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (overflowOperator n : HilbertOperator (Qubits (n + n + 1)))
      ((overflowEncoding n).encode state) output).symm.trans semantic
  exact circuitColumn.trans semanticColumn.symm

/-- The literal gates retain every supplied operand and the explicit carry-output bit. -/
def completeOverflowProgram (n : Nat) : UnitaryCircuit (Qubits (overflowEncoding n).width) :=
  .seq (overflowProgram n)
    (.identity (Qubits (overflowEncoding n).width) (List.range (n + n + 1)) List.nodup_range)

/-- Retaining the full supplied frame adds no mathematical action. -/
theorem ttkCompleteOverflow_matrix (n : Nat) :
    (completeOverflowProgram n).matrix = overflowOperator n := by
  have unchanged : (completeOverflowProgram n).matrix = (overflowProgram n).matrix := by
    apply Subtype.ext
    change (1 : HilbertOperator (Qubits (overflowEncoding n).width)) *
      ((overflowProgram n).matrix : HilbertOperator (Qubits (overflowEncoding n).width)) = _
    exact one_mul _
  exact unchanged.trans (ttkOverflow_matrix n)

/-- Exactly two operand words and one explicit output bit remain live at all widths. -/
theorem ttkCompleteOverflow_physical (n : Nat) :
    (completeOverflowProgram n).physical_idx = List.range (n + n + 1) := by
  change (overflowProgram n).physical_idx ∪ List.range (n + n + 1) = List.range (n + n + 1)
  apply List.Subset.union_eq_right
  simpa only [two_mul] using (ttkOverflow_interface n).2

/-- Retaining the supplied frame emits no additional event. -/
theorem ttkCompleteOverflow_eventCost (n : Nat) :
    (completeOverflowProgram n).eventCost = (overflowProgram n).eventCost := by
  simp only [completeOverflowProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

/-- Actual serial unit-duration depth, including the two distinct boundary cases. -/
theorem ttkCompleteOverflow_depth (n : Nat) :
    (completeOverflowProgram n).evaluatedEventDepth (fun _ => 1) =
      n + 4 * (n - 1) + 2 * (n - 2) +
        (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  rw [completeOverflowProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  change (overflowProgram n).evaluatedEventDepth (fun _ => 1) + 0 = _
  rw [add_zero, ttkOverflow_serial_depth]

end

end QuantumAlg.MAU.Addition.TTK
