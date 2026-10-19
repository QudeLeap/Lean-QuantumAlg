/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Conjugation
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.FrameBasis
import all QuantumAlg.Core.Base.Gate.VectorChain
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Recompute

/-!
# Complete actual division basis action with its measured amplitude

The operator is the one already identified with the actual retained-store
block of InPlaceDivision.body. Its forward/product/HZX/backward/correction/
swap sequence takes the original full prepared frame to the full restored
frame and canonical quotient. Each stored finite result has precisely the
Hadamard amplitude 1/sqrt(2^n), with its original Y Walsh phase cancelled
by the actually selected native correction. Every external-reference
basis coordinate is unchanged [LYL+26, sec_point_add/sec_point_add.tex:45-105].

The only arithmetic domain is original prime modulus, 0<X<p and Y<p.
Y=0 remains valid. The classical source fiber and its aggregation belong
to the actual write semantics proved separately; no branch probability
or caller-supplied arithmetic behavior is assumed here.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceDivisionBasis

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement ProductPlacement
open InPlaceArithmetic NumeratorFrameBasis

/-- Every actual stored branch maps the full initial frame to the quotient with exact amplitude. -/
lemma operator_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index) :
    (InPlaceDivisionConjugation.operator environment modulus prime Reference stored).applyVec
      (ket modulus.size (InitialPortProgram.inputFrame modulus value, numerator) reference).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (ket modulus.size (InitialPortProgram.inputFrame modulus value,
          InPlaceRecompute.saved modulus value numerator positive bounded) reference).vec := by
  let completed := InPlaceForward.result modulus value.val positive bounded
  let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus)
    (completed, numerator)
  let recovered := InPlaceRecompute.recovered modulus value numerator positive bounded
  have forward := native_normalized (environment := environment) modulus.size
    (NativeEEAFrame.forward modulus prime)
    (InitialPortProgram.inputFrame modulus value, numerator) (completed, numerator)
    (NativeEEAFrame.forward_initial modulus prime value numerator positive bounded) reference
  have product := native_normalized (environment := environment) modulus.size
    (NativeProductFrame.program modulus.size (modulusWord modulus))
    (completed, numerator) multiplied
    ((NativeProductFrame.nativeProductFrame_realizes modulus.size
      (modulusWord modulus)).apply_encoded_ket (completed, numerator)) reference
  have numeratorKept : multiplied.2 = numerator := by
    have actual := ProductPortLaws.step_numerator modulus.size (modulusWord modulus)
      (completed, numerator)
    rw [ProductReadout.numerator_eq, ProductReadout.numerator_eq] at actual
    exact actual
  have measured : (NumeratorResetConjugation.operator environment modulus.size Reference
    stored).applyVec
      (ket modulus.size multiplied reference).vec =
      (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input modulus.size)))
          numerator) • (ket modulus.size (multiplied.1, 0) reference).vec := by
    have actual := NumeratorBranchAction.operator_ket (environment := environment) modulus.size
      stored
      (basis modulus.size multiplied) reference
    rw [NumeratorFrameBasis.word, NumeratorFrameBasis.replace, numeratorKept] at actual
    exact actual
  have backward := native_normalized (environment := environment) modulus.size
    (NativeEEAFrame.backward modulus prime)
    (multiplied.1, 0) recovered
    (backward_reset_ket modulus prime value numerator positive bounded) reference
  have mask : QubitReadouts.mask (stored.read (input modulus.size)) =
      (fun index =>
        (NumeratorReset.outcome (stored.read (input modulus.size))).val.testBit index.val) := by
    funext index
    exact (NumeratorReset.outcome_bit (stored.read (input modulus.size)) index).symm
  have correctionNative :
      ((NumeratorCorrection.member modulus.size (modulusWord modulus)
        (stored.read (input modulus.size))).applyVec environment)
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode recovered))).vec =
      WalshHadamard.walshSign
        (NumeratorReset.outcome (stored.read (input modulus.size))) numerator •
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode recovered))).vec := by
    change ((ReusedProduct.correction modulus.size (modulusWord modulus)
      (QubitReadouts.mask (stored.read (input modulus.size)))).applyVec environment) _ = _
    rw [mask]
    exact InPlaceRecompute.correction_ket modulus prime value numerator
      (NumeratorReset.outcome (stored.read (input modulus.size)))
      positive bounded numeratorBound
  have correction := native_action (environment := environment) modulus.size
    (NumeratorCorrection.member modulus.size (modulusWord modulus)
      (stored.read (input modulus.size))) recovered recovered
    (WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input modulus.size))) numerator)
    correctionNative reference
  have swap := native_normalized (environment := environment) modulus.size (FrameSwap.program
    modulus.size) recovered
    (InitialPortProgram.inputFrame modulus value,
      InPlaceRecompute.saved modulus value numerator positive bounded)
    (FrameSwapReadout.program_reused_ket modulus.size
      (InitialPortProgram.inputFrame modulus value,
        InPlaceRecompute.saved modulus value numerator positive bounded)) reference
  have combined := HilbertOperator.applyVec_six
    (forward.trans (one_smul ℂ _).symm)
    (product.trans (one_smul ℂ _).symm)
    measured
    (backward.trans (one_smul ℂ _).symm)
    correction
    (swap.trans (one_smul ℂ _).symm)
  have scalar :
      (1 : ℂ) * 1 * (WalshHadamard.invSqrtCard modulus.size *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (input modulus.size))) numerator) * 1 *
        WalshHadamard.walshSign
          (NumeratorReset.outcome (stored.read (input modulus.size))) numerator * 1 =
      WalshHadamard.invSqrtCard modulus.size := by
    simp only [one_mul, mul_one, mul_assoc, WalshHadamard.walshSign_mul_self]
  exact combined.trans (congrArg (fun scalar : ℂ => scalar •
    (ket modulus.size (InitialPortProgram.inputFrame modulus value,
      InPlaceRecompute.saved modulus value numerator positive bounded) reference).vec) scalar)

end

end QuantumAlg.MeasuredUncompute.InPlaceDivisionBasis
