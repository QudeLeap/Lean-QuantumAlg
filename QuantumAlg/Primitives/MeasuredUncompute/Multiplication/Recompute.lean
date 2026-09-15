/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Multiplication.Arithmetic
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap.Readout

/-!
# Exact multiplication correction, inverse recovery and actual final swap

After the reused forward EEA, actual X-inverse times saved X*Y recomputes
old Y. The literal selected Z and product adjoint cancel its measured
Walsh character. The same reused EEA backward restores X and Γ, then the
actual three-CNOT-per-bit swap places saved X*Y in Y and restores A=0
[LYL+26, sec_point_add/sec_point_add.tex:119-122].

These equations apply the existing emitted programs to complete labels
and their actual phase amplitudes. They preserve numerator zero; only
original X is nonzero. The runtime H/Z/classical-store semantics is a
separate composition obligation for the one actual multiplication circuit.
-/

namespace QuantumAlg.MeasuredUncompute.MultiplicationRecompute

noncomputable section

open ProductPlacement ProductReadout MAU.Inversion.SharedEEA
open InPlaceArithmetic MultiplicationArithmetic

/-- Actual recomputation retains every other word, padding bit and EEA history bit. -/
theorem compute_frame (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ReusedProduct.computeStep modulus.size (modulusWord modulus)
        (inverseFrame modulus value numerator positive bounded) =
      ((inverseFrame modulus value numerator positive bounded).1, numerator) := by
  let state := inverseFrame modulus value numerator positive bounded
  apply ProductPortLaws.frame_ext
  · exact (ReusedProductPortLaws.compute_input modulus.size (modulusWord modulus) state).trans
      (input_pair modulus.size state.1 state.2 numerator)
  · rw [numerator_eq, numerator_eq]
    exact recomputed_numerator modulus prime value numerator positive bounded numeratorBound
  · exact (ReusedProductPortLaws.compute_accumulator modulus.size (modulusWord modulus) state).trans
      (accumulator_pair modulus.size state.1 state.2 numerator)
  · exact (ReusedProductPortLaws.compute_history modulus.size (modulusWord modulus) state).trans
      (history_pair modulus.size state.1 state.2 numerator)

/-- The full recomputation equation is realized by the literal existing product gate program. -/
theorem compute_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (ReusedProduct.compute modulus.size (modulusWord modulus)).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            (inverseFrame modulus value numerator positive bounded))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          ((inverseFrame modulus value numerator positive bounded).1, numerator)) := by
  have actual := (ReusedProduct.reusedProduct_realizes modulus.size
    (modulusWord modulus)).apply_encoded_ket (inverseFrame modulus value numerator positive bounded)
  rw [compute_frame modulus prime value numerator positive bounded numeratorBound] at actual
  exact actual

/-- The actual selected recompute/Z/uncompute attaches exactly the original Y Walsh character. -/
theorem correction_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).applyVec
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            (inverseFrame modulus value numerator positive bounded))).vec =
      WalshHadamard.walshSign outcome numerator •
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            (inverseFrame modulus value numerator positive bounded))).vec := by
  have actual := ReusedProduct.correction_ket modulus.size (modulusWord modulus) outcome
    (inverseFrame modulus value numerator positive bounded)
  rw [recomputed_numerator modulus prime value numerator positive bounded numeratorBound] at actual
  exact actual

/-- The actual correction cancels the measured phase while retaining the complete inverse frame. -/
theorem correction_cancels (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
            ((frameEncoding modulus.size).encode
              (inverseFrame modulus value numerator positive bounded))).vec) =
      (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (inverseFrame modulus value numerator positive bounded))).vec := by
  rw [UnitaryCircuit.applyVec_smul,
    correction_ket modulus prime value numerator outcome positive bounded numeratorBound,
    smul_smul, WalshHadamard.walshSign_mul_self, one_smul]

/-- The actual same reused adjoint restores the full seed while preserving the saved product. -/
theorem backward_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    (NativeEEAFrame.backward modulus prime).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            (inverseFrame modulus value numerator positive bounded))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode (resetFrame modulus value numerator)) :=
  NativeEEAFrame.backward_result modulus prime value (saved modulus value numerator)
    positive bounded

/-- Actual correction, same EEA backward and literal swap return X*Y in Y and restore all Γ. -/
theorem correction_backward_swap (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).seq
        ((NativeEEAFrame.backward modulus prime).seq (FrameSwap.program modulus.size))).applyVec
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
            ((frameEncoding modulus.size).encode
              (inverseFrame modulus value numerator positive bounded))).vec) =
      (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (InitialPortProgram.inputFrame modulus value, saved modulus value numerator))).vec := by
  rw [UnitaryCircuit.applyVec_seq,
    correction_cancels modulus prime value numerator outcome positive bounded numeratorBound,
    UnitaryCircuit.applyVec_seq]
  have backward := congrArg
    (fun state : NormalizedVector (Qubits (frameEncoding modulus.size).width) => state.vec)
    (backward_ket modulus prime value numerator positive bounded)
  change (NativeEEAFrame.backward modulus prime).applyVec
    (NormalizedVector.ket ((frameEncoding modulus.size).encode
      (inverseFrame modulus value numerator positive bounded))).vec = _ at backward
  rw [backward]
  have swap := congrArg
    (fun state : NormalizedVector (Qubits (frameEncoding modulus.size).width) => state.vec)
    (FrameSwapReadout.program_reused_ket modulus.size
      (InitialPortProgram.inputFrame modulus value, saved modulus value numerator))
  exact swap

end

end QuantumAlg.MeasuredUncompute.MultiplicationRecompute
