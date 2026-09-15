/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.PortLaws
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.Readout
import all QuantumAlg.Primitives.MeasuredUncompute.Native.EEAFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.BitValues
import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse

/-!
# Complete arithmetic frames at the measured-division inverse boundary

The actual forward EEA returns X's inverse and zero A. The actual native
product writes X-inverse times Y into A while retaining all small history.
Replacing the measured Y word by its actual reset label zero therefore
gives exactly the input of the same EEA adjoint on the reused workspace
[LYL+26, sec_point_add/sec_point_add.tex:51-81].

These are complete word and frame equations. The measurement interpreter
must still establish the reset label and its branch amplitude; no unitary
reset, extra execution framework, or omitted history is assumed here.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceArithmetic

noncomputable section

open ProductPlacement ProductReadout MAU.Inversion SharedEEA
open NumberTheory.SharedEEA

/-- The original modulus fits the exact native product parameter at its own binary width. -/
def modulusWord (modulus : Nat) : Fin (2 ^ modulus.size + 1) :=
  ⟨modulus, (Nat.lt_size_self modulus).trans (Nat.lt_succ_self _)⟩

private theorem input_pair (width : Nat) (state : Registers width)
    (left right : Fin (2 ^ width)) :
    input width (state, left) = input width (state, right) := rfl

private theorem accumulator_pair (width : Nat) (state : Registers width)
    (left right : Fin (2 ^ width)) :
    accumulator width (state, left) = accumulator width (state, right) := rfl

private theorem history_before_numerator (width : Nat) (index : Fin (historyWidth width)) :
    (historyWire width index).val < (encoding width).width := by
  have bound := index.isLt
  rw [encoding_width]
  change (if index.val < 6 then width + index.val else 2 * width + index.val) < _
  unfold historyWidth tailWidth at bound
  split_ifs <;> omega

private theorem history_pair (width : Nat) (state : Registers width)
    (left right : Fin (2 ^ width)) :
    history width (state, left) = history width (state, right) := by
  apply word_ext
  intro index
  simp only [history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
  let shared : Fin (encoding width).width :=
    ⟨(historyWire width index).val, history_before_numerator width index⟩
  have position : (historyWire width index).rev.val = width + shared.rev.val := by
    simp only [Fin.val_rev]
    change (encoding width).width + width - ((historyWire width index).val + 1) =
      width + ((encoding width).width - ((historyWire width index).val + 1))
    have within := history_before_numerator width index
    omega
  rw [position]
  exact (prodEquiv_testBit_left ((encoding width).encode state) left shared.rev).trans
    (prodEquiv_testBit_left ((encoding width).encode state) right shared.rev).symm

/-- The physical X read of the original fixed entry is precisely its arbitrary supplied input. -/
theorem initial_input (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    input modulus.size (InitialPortProgram.inputFrame modulus value, numerator) = value := by
  apply word_ext
  intro index
  rw [input, readWord_bit, FramePorts.input_read, InitialPortProgram.inputFrame_input]
  have actual := InitialBitValues.secondWord_input modulus value index
  rw [secondWordBit_get] at actual
  exact actual

/-- The original A port is actually zero before its separately charged fixed constant load. -/
theorem initial_accumulator (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    accumulator modulus.size (InitialPortProgram.inputFrame modulus value, numerator) = 0 := by
  apply word_ext
  intro index
  rw [accumulator, readWord_bit, FramePorts.accumulator_read,
    InitialPortProgram.inputFrame_large_bit]
  simp only [Fin.val_zero, Nat.zero_testBit]

/-- The full forward result's physical X value is the independently specified residue inverse. -/
theorem forward_input (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    input modulus.size (InPlaceForward.result modulus value.val positive bounded, numerator) =
      CanonicalInverse.word modulus prime.pos value.val := by
  have source :
      input modulus.size (InPlaceForward.result modulus value.val positive bounded, numerator) =
        InverseOutput.word modulus value.val positive bounded := by
    apply word_ext
    intro index
    rw [input, readWord_bit, FramePorts.input_read, InPlaceForward.result_input_port]
    have actual := InitialBitValues.secondWord_input modulus
      (InverseOutput.word modulus value.val positive bounded) index
    rw [secondWordBit_get] at actual
    exact actual
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  exact source.trans (CanonicalInverse.source_eq_word modulus value.val coprime positive bounded)

/-- The complete forward gate proof discharges clean A internally on the original prime domain. -/
theorem forward_accumulator (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    accumulator modulus.size
      (InPlaceForward.result modulus value.val positive bounded, numerator) = 0 := by
  apply word_ext
  intro index
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  rw [accumulator, readWord_bit, FramePorts.accumulator_read,
    InPlaceForward.result_large_bit modulus value.val coprime positive bounded]
  simp only [Fin.val_zero, Nat.zero_testBit]

/-- The actual native product writes the canonical inverse times Y into the existing A port. -/
theorem product_quotient (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    (accumulator modulus.size (NativeProductFrame.step modulus.size (modulusWord modulus)
      (InPlaceForward.result modulus value.val positive bounded, numerator))).val =
        ((CanonicalInverse.word modulus prime.pos value.val).val * numerator.val) % modulus := by
  have valid : (accumulator modulus.size
      (InPlaceForward.result modulus value.val positive bounded, numerator)).val <
        (modulusWord modulus).val := by
    rw [forward_accumulator modulus prime value numerator positive bounded]
    exact prime.pos
  have actual := ProductPortLaws.step_accumulator modulus.size (modulusWord modulus)
    (InPlaceForward.result modulus value.val positive bounded, numerator) valid
  rw [forward_accumulator modulus prime value numerator positive bounded,
    forward_input modulus prime value numerator positive bounded, numerator_eq] at actual
  have nativeModulus : (modulusWord modulus).val = modulus := rfl
  simpa only [Fin.val_zero, Nat.zero_add, nativeModulus] using actual

private theorem zero_accumulator_reset (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Registers width) (numerator : Fin (2 ^ width))
    (clean : accumulator width (state, numerator) = 0) :
    let multiplied := NativeProductFrame.step width modulus (state, numerator)
    (multiplied.1, 0) = (WorkspaceReuse.placement width).grouping.symm
      (state, accumulator width multiplied) := by
  dsimp only
  let multiplied := NativeProductFrame.step width modulus (state, numerator)
  apply ProductPortLaws.frame_ext
  · rw [ReusedProductReadout.input_symm]
    exact (input_pair width multiplied.1 0 multiplied.2).trans
      ((ProductPortLaws.step_input width modulus (state, numerator)).trans
        (input_pair width state numerator (accumulator width multiplied)))
  · rw [numerator_eq, ReusedProductReadout.numerator_symm]
    exact (clean.symm.trans
      (accumulator_pair width state numerator (accumulator width multiplied)))
  · rw [ReusedProductReadout.accumulator_symm, numerator_eq]
    exact accumulator_pair width multiplied.1 0 multiplied.2
  · rw [ReusedProductReadout.history_symm]
    exact (history_pair width multiplied.1 0 multiplied.2).trans
      ((product_history width modulus (state, numerator)).trans
        (history_pair width state numerator (accumulator width multiplied)))

/-- Reset Y gives exactly the same adjoint's required complete frame, including the full Γ. -/
theorem reset_for_backward (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    let completed := InPlaceForward.result modulus value.val positive bounded
    let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus)
      (completed, numerator)
    (multiplied.1, 0) = (WorkspaceReuse.placement modulus.size).grouping.symm
      (completed, accumulator modulus.size multiplied) :=
  zero_accumulator_reset modulus.size (modulusWord modulus) _ numerator
    (forward_accumulator modulus prime value numerator positive bounded)

/-- The actual reused EEA adjoint restores X and fixed small state,
while retaining the saved quotient. -/
theorem backward_reset_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    let completed := InPlaceForward.result modulus value.val positive bounded
    let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus)
      (completed, numerator)
    (NativeEEAFrame.backward modulus prime).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode (multiplied.1, 0))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            (InitialPortProgram.inputFrame modulus value,
              accumulator modulus.size multiplied))) := by
  dsimp only
  rw [reset_for_backward modulus prime value numerator positive bounded]
  exact NativeEEAFrame.backward_result modulus prime value _ positive bounded

end

end QuantumAlg.MeasuredUncompute.InPlaceArithmetic
