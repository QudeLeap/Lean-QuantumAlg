/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.PhaseMatrix
import all QuantumAlg.Primitives.QFT.Source.PhaseMatrix
import all QuantumAlg.Primitives.QFT.Source.BinaryEntries
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Components.Gates.Operator
import Mathlib.Algebra.BigOperators.Fin

/-!
# Matrix recurrence of the actual native QFT

The leading Hadamard, complete controlled phases and recursive tail have
the same exact matrix recurrence as the positive-phase Fourier transform.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

private lemma phase_binaryMatrix_pair (oracles : OracleModel) (n : Nat)
    (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    onBinaryLabels (phaseLayer oracles n) environment (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      if outputHead = inputHead ∧ outputTail = inputTail then
        (if inputHead = 1 then ω (n + 1) ^ inputTail.val else 1)
      else 0 := by
  rw [qftSource_phase_binaryMatrix_entry (environment := environment), qftPairEquiv_testBit_high,
    qftPairEquiv_mod_tail]
  simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq, decide_eq_true_eq]

private lemma phaseAfterLeading_binaryMatrix_pair (oracles : OracleModel) (n : Nat)
    (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    ((onBinaryLabels (phaseLayer oracles n) environment : HilbertOperator (Qubits (n + 1))) *
      (onBinaryLabels (leadingHadamard oracles n) environment : HilbertOperator (Qubits (n + 1))))
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      (if outputHead = 1 then ω (n + 1) ^ outputTail.val else 1) *
        Gate.HOp outputHead inputHead * (if outputTail = inputTail then 1 else 0) := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp (qftPairEquiv n), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single outputHead]
  · rw [Finset.sum_eq_single outputTail]
    · by_cases same : outputTail = inputTail <;>
        simp [phase_binaryMatrix_pair (environment := environment),
          qftSource_leading_binaryMatrix_pair (environment := environment), same]
    · intro candidate _ different
      simp [phase_binaryMatrix_pair (environment := environment), Ne.symm different]
    · simp
  · intro candidate _ different
    simp [phase_binaryMatrix_pair (environment := environment), Ne.symm different]
  · simp

lemma qftSource_noSwap_succ_binaryMatrix_pair (oracles : OracleModel) (n : Nat)
    (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    onBinaryLabels (noSwap oracles (n + 1)) environment (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      onBinaryLabels (noSwap oracles n) environment outputTail inputTail *
        (if outputHead = 1 then ω (n + 1) ^ inputTail.val else 1) *
          Gate.HOp outputHead inputHead := by
  rw [noSwap, qftSource_binaryMatrix_seq (environment := environment), qftSource_binaryMatrix_seq
    (environment := environment)]
  change (((onBinaryLabels (tailLayer oracles n (noSwap oracles n)) environment :
      HilbertOperator (Qubits (n + 1))) *
    (onBinaryLabels (phaseLayer oracles n) environment : HilbertOperator (Qubits (n + 1)))) *
    (onBinaryLabels (leadingHadamard oracles n) environment : HilbertOperator (Qubits (n + 1))))
      (qftPairEquiv n (outputHead, outputTail))
      (qftPairEquiv n (inputHead, inputTail)) = _
  rw [mul_assoc, Matrix.mul_apply,
    ← Equiv.sum_comp (qftPairEquiv n), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single outputHead]
  · rw [Finset.sum_eq_single inputTail]
    · rw [qftSource_tail_binaryMatrix_pair (environment := environment),
      phaseAfterLeading_binaryMatrix_pair (environment := environment)]
      simp
      ring_nf
    · intro candidate _ different
      rw [qftSource_tail_binaryMatrix_pair (environment := environment),
        phaseAfterLeading_binaryMatrix_pair (environment := environment)]
      simp [different]
    · simp
  · intro candidate _ different
    apply Finset.sum_eq_zero
    intro candidateTail _
    rw [qftSource_tail_binaryMatrix_pair (environment := environment)]
    simp [Ne.symm different]
  · simp

end

end QuantumAlg.QuantumFourierTransform.Source
