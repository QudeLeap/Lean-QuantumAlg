/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication.Conjugation
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.FrameBasis
import all QuantumAlg.Core.Base.Gate.VectorChain
import all QuantumAlg.Primitives.MeasuredUncompute.Multiplication.Recompute

/-!
# Complete actual multiplication basis action with its measured amplitude

The operator is the one identified with the actual retained-store block
of InPlaceMultiplication.body. The initial product saves X*Y, H/Z/reset
supplies the existing reused workspace, and actual EEA on nonzero X
permits exact recomputation of old Y. The stored Z correction cancels its
Walsh character, the identical EEA backward restores X and Γ, and the real
swap returns the saved product. Every stored finite vector has precisely
the amplitude 1/sqrt(2^n) and retains the same external-reference label
[LYL+26, sec_point_add/sec_point_add.tex:32-36,119-122].

Only original X is nonzero; Y and the saved product may be zero. No inverse
of Y or of the product is introduced. The actual classical source fibers
and density extension are separate consequences of the shared interpreter.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceMultiplicationBasis

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement ProductPlacement
open InPlaceArithmetic MultiplicationArithmetic NumeratorFrameBasis

/-- Every actual stored branch outputs the product, restored full seed and exact amplitude. -/
theorem operator_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index) :
    (InPlaceMultiplicationConjugation.operator modulus prime Reference stored).applyVec
      (ket modulus.size (InitialPortProgram.inputFrame modulus value, numerator) reference).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (ket modulus.size (InitialPortProgram.inputFrame modulus value,
          saved modulus value numerator) reference).vec := by
  let initial := (InitialPortProgram.inputFrame modulus value, numerator)
  let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus) initial
  let inverse := inverseFrame modulus value numerator positive bounded
  let restored := resetFrame modulus value numerator
  have product := native_normalized modulus.size
    (NativeProductFrame.program modulus.size (modulusWord modulus)) initial multiplied
    ((NativeProductFrame.nativeProductFrame_realizes modulus.size
      (modulusWord modulus)).apply_encoded_ket initial) reference
  have numeratorKept : multiplied.2 = numerator := by
    have actual := ProductPortLaws.step_numerator modulus.size (modulusWord modulus) initial
    rw [ProductReadout.numerator_eq, ProductReadout.numerator_eq] at actual
    exact actual
  have reset : (multiplied.1, 0) = restored := reset_frame modulus value numerator
  have measured : (NumeratorResetConjugation.operator modulus.size Reference stored).applyVec
      (ket modulus.size multiplied reference).vec =
      (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input modulus.size)))
          numerator) • (ket modulus.size restored reference).vec := by
    have actual := NumeratorBranchAction.operator_ket modulus.size stored
      (basis modulus.size multiplied) reference
    rw [NumeratorFrameBasis.word, NumeratorFrameBasis.replace, numeratorKept] at actual
    have resetKet := congrArg
      (fun frame : Frame modulus.size => (ket modulus.size frame reference).vec) reset
    exact actual.trans (congrArg (fun vector =>
      (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input modulus.size)))
          numerator) • vector) resetKet)
  have forward := native_normalized modulus.size (NativeReusedEEA.forward modulus prime)
    restored inverse (forward_ket modulus prime value numerator positive bounded) reference
  have mask : QubitReadouts.mask (stored.read (input modulus.size)) =
      (fun index =>
        (NumeratorReset.outcome (stored.read (input modulus.size))).val.testBit index.val) := by
    funext index
    exact (NumeratorReset.outcome_bit (stored.read (input modulus.size)) index).symm
  have correctionNative :
      (NumeratorCorrection.member modulus.size (modulusWord modulus)
        (stored.read (input modulus.size))).applyVec
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode inverse))).vec =
      WalshHadamard.walshSign
        (NumeratorReset.outcome (stored.read (input modulus.size))) numerator •
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode inverse))).vec := by
    change (ReusedProduct.correction modulus.size (modulusWord modulus)
      (QubitReadouts.mask (stored.read (input modulus.size)))).applyVec _ = _
    rw [mask]
    exact MultiplicationRecompute.correction_ket modulus prime value numerator
      (NumeratorReset.outcome (stored.read (input modulus.size)))
      positive bounded numeratorBound
  have correction := native_action modulus.size
    (NumeratorCorrection.member modulus.size (modulusWord modulus)
      (stored.read (input modulus.size))) inverse inverse
    (WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input modulus.size))) numerator)
    correctionNative reference
  have backward := native_normalized modulus.size (NativeEEAFrame.backward modulus prime)
    inverse restored (MultiplicationRecompute.backward_ket modulus prime value numerator
      positive bounded) reference
  have swap := native_normalized modulus.size (FrameSwap.program modulus.size) restored
    (InitialPortProgram.inputFrame modulus value, saved modulus value numerator)
    (FrameSwapReadout.program_reused_ket modulus.size
      (InitialPortProgram.inputFrame modulus value, saved modulus value numerator)) reference
  have combined := HilbertOperator.applyVec_six
    (product.trans (one_smul ℂ _).symm)
    measured
    (forward.trans (one_smul ℂ _).symm)
    correction
    (backward.trans (one_smul ℂ _).symm)
    (swap.trans (one_smul ℂ _).symm)
  have scalar :
      (1 : ℂ) * (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (input modulus.size))) numerator) * 1 *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (input modulus.size))) numerator * 1 * 1 =
      WalshHadamard.invSqrtCard modulus.size := by
    simp only [one_mul, mul_one, mul_assoc, WalshHadamard.walshSign_mul_self]
  exact combined.trans (congrArg (fun scalar : ℂ => scalar •
    (ket modulus.size (InitialPortProgram.inputFrame modulus value,
      saved modulus value numerator) reference).vec) scalar)

end

end QuantumAlg.MeasuredUncompute.InPlaceMultiplicationBasis
