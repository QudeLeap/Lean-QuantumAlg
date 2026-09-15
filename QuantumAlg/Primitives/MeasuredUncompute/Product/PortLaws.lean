/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Readout

/-!
# Exact arithmetic at the existing product ports

The real product placement reads X, Y, A and every retained padding and
history bit. These complete reads determine the full frame. The actual
native product preserves X, Y and that entire history, and accumulates
their modular product into A [LYL+26, sec_point_add/sec_point_add.tex:51-63].
The canonical accumulator condition is the existing multiplication
contract; the division consumer establishes it from its actual A=0
preparation. No auxiliary state is omitted from the resulting equations.
-/

namespace QuantumAlg.MeasuredUncompute.ProductPortLaws

noncomputable section

open ProductPlacement ProductReadout MAU.Multiplication

/-- Four independent complete physical reads determine every bit of the live frame. -/
theorem frame_ext {width : Nat} {left right : Frame width}
    (sameInput : input width left = input width right)
    (sameNumerator : numerator width left = numerator width right)
    (sameAccumulator : accumulator width left = accumulator width right)
    (sameHistory : history width left = history width right) : left = right := by
  apply (placement width).grouping.injective
  apply Prod.ext
  · apply Prod.ext
    · exact (grouping_input width left).trans (sameInput.trans (grouping_input width right).symm)
    · apply Prod.ext
      · exact (grouping_numerator width left).trans
          (sameNumerator.trans (grouping_numerator width right).symm)
      · exact (grouping_accumulator width left).trans
          (sameAccumulator.trans (grouping_accumulator width right).symm)
  · exact (grouping_history width left).trans
      (sameHistory.trans (grouping_history width right).symm)

private theorem grouping_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) :
    (placement width).grouping (NativeProductFrame.step width modulus state) =
      (VariableGidney.prefixOutput modulus width ((placement width).grouping state).1,
        ((placement width).grouping state).2) :=
  (placement width).grouping.apply_symm_apply _

/-- The native product leaves the complete X word unchanged on every basis frame. -/
theorem step_input (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    input width (NativeProductFrame.step width modulus state) = input width state := by
  rw [← grouping_input, ← grouping_input]
  have actual := congrArg
    (fun value : VariableGidney.Registers width × Fin (2 ^ historyWidth width) =>
    value.1.1) (grouping_step width modulus state)
  exact actual

/-- The native product leaves the complete existing Y word unchanged on every basis frame. -/
theorem step_numerator (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    numerator width (NativeProductFrame.step width modulus state) = numerator width state := by
  rw [← grouping_numerator, ← grouping_numerator]
  have actual := congrArg
    (fun value : VariableGidney.Registers width × Fin (2 ^ historyWidth width) =>
    value.1.2.1) (grouping_step width modulus state)
  exact actual

/-- A receives the exact modular product; no high padding or history coordinate is discarded. -/
theorem step_accumulator (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width)
    (valid : (accumulator width state).val < modulus.val) :
    (accumulator width (NativeProductFrame.step width modulus state)).val =
      ((accumulator width state).val + (input width state).val *
        (numerator width state).val) % modulus.val := by
  have groupedValid : ((placement width).grouping state).1.2.2.val < modulus.val := by
    rw [grouping_accumulator]
    exact valid
  have arithmetic :=
    (VariableGidney.variableGidney_valid width modulus
      ((placement width).grouping state).1 groupedValid).2.2
  have actual := congrArg
    (fun value : VariableGidney.Registers width × Fin (2 ^ historyWidth width) => value.1.2.2.val)
    (grouping_step width modulus state)
  rw [grouping_accumulator] at actual
  rw [grouping_input, grouping_numerator, grouping_accumulator] at arithmetic
  exact actual.trans arithmetic

/-- Complete physical readout equations identify the actual native output frame. -/
theorem step_eq_of_reads (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state result : Frame width) (valid : (accumulator width state).val < modulus.val)
    (readInput : input width result = input width state)
    (readNumerator : numerator width result = numerator width state)
    (readAccumulator : (accumulator width result).val =
      ((accumulator width state).val + (input width state).val *
        (numerator width state).val) % modulus.val)
    (readHistory : history width result = history width state) :
    NativeProductFrame.step width modulus state = result := by
  apply frame_ext
  · exact (step_input width modulus state).trans readInput.symm
  · exact (step_numerator width modulus state).trans readNumerator.symm
  · exact Fin.ext ((step_accumulator width modulus state valid).trans readAccumulator.symm)
  · exact (product_history width modulus state).trans readHistory.symm

/-- The same actual gate program realizes the complete frame identified by the physical reads. -/
theorem program_output_of_reads (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state result : Frame width) (valid : (accumulator width state).val < modulus.val)
    (readInput : input width result = input width state)
    (readNumerator : numerator width result = numerator width state)
    (readAccumulator : (accumulator width result).val =
      ((accumulator width state).val + (input width state).val *
        (numerator width state).val) % modulus.val)
    (readHistory : history width result = history width state) :
    (NativeProductFrame.program width modulus).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
          ((frameEncoding width).encode state)) =
      NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode result) := by
  have actual :=
    (NativeProductFrame.nativeProductFrame_realizes width modulus).apply_encoded_ket state
  rw [step_eq_of_reads width modulus state result valid readInput readNumerator
    readAccumulator readHistory] at actual
  exact actual

end

end QuantumAlg.MeasuredUncompute.ProductPortLaws
