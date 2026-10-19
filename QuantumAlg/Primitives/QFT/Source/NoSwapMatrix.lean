/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.Recurrence
import all QuantumAlg.Primitives.QFT.Source.Recurrence
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Util.Complex
import Mathlib.Tactic.FinCases

/-!
# Closed Fourier matrix before the final native swaps

The actual recursively composed native word has the original normalized
positive-phase Fourier entries with the output bits reversed.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

open NormalizedVector

noncomputable section

private lemma hadamard_entry (output input : Fin 2) :
    Gate.HOp output input =
      invSqrt2 * (if output = 1 ∧ input = 1 then -1 else 1) := by
  fin_cases output <;> fin_cases input <;> simp [Gate.HOp]

/-- Closed matrix formula for the actual recursive no-swap circuit.  Its row
label is bit-reversed because the final symmetric SWAP network has not yet
been applied. -/
lemma qftSource_noSwap_binaryMatrix_entry (oracles : OracleModel) (n : Nat)
    (output input : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    onBinaryLabels (noSwap oracles n) environment output input =
      invSqrtN n *
        ω n ^ ((qftReverseBits n output).val * input.val) := by
  induction n with
  | zero =>
      fin_cases output
      fin_cases input
      rw [noSwap, qftSource_binaryMatrix_identity (environment := environment)]
      norm_num [invSqrtN]
  | succ n ih =>
      rcases (qftPairEquiv n).surjective output with
        ⟨⟨outputHead, outputTail⟩, rfl⟩
      rcases (qftPairEquiv n).surjective input with
        ⟨⟨inputHead, inputTail⟩, rfl⟩
      rw [qftSource_noSwap_succ_binaryMatrix_pair (environment := environment), ih,
        qftReverseBits_pair, qftPairEquiv_apply_val, invSqrtN_succ,
        hadamard_entry]
      calc
        (invSqrtN n *
              ω n ^ ((qftReverseBits n outputTail).val * inputTail.val)) *
            (if outputHead = 1 then
              ω (n + 1) ^ inputTail.val else 1) *
              (invSqrt2 *
                (if outputHead = 1 ∧ inputHead = 1 then -1 else 1)) =
            invSqrt2 * invSqrtN n *
              (ω n ^
                    ((qftReverseBits n outputTail).val * inputTail.val) *
                (if outputHead = 1 then
                  ω (n + 1) ^ inputTail.val else 1) *
                (if outputHead = 1 ∧ inputHead = 1 then -1 else 1)) := by
              ring
        _ = invSqrt2 * invSqrtN n *
              ω (n + 1) ^
                ((2 * (qftReverseBits n outputTail).val + outputHead.val) *
                  (inputTail.val + 2 ^ n * inputHead.val)) := by
              rw [qftOmega_pair_recurrence]

end

end QuantumAlg.QuantumFourierTransform.Source
