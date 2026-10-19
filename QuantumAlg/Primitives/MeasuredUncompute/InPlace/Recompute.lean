/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.PortLaws
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap.Readout

/-!
# Actual recomputation, phase cancellation and final division output

The saved A value is read from the actual forward EEA/product result.
After the identical EEA adjoint has restored X, the actual X/A/Y product
recomputes the original numerator, including numerator zero. Its literal
selected Z sequence and identical product adjoint cancel exactly the
measured Walsh character. The real final three-CNOT-per-bit swap returns
the quotient to the original Y port and restores A and the full fixed
small frame [LYL+26, sec_point_add/sec_point_add.tex:75-105].

Only X is nonzero. The word bounds below are the original canonical
prime-residue domain, not additional workspace or coefficient conditions.
The measurement interpreter supplies its actual branch amplitude; these
equalities apply the existing emitted unitary programs to that amplitude.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceRecompute

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ProductPlacement ProductReadout MAU.Inversion SharedEEA
open NumberTheory.SharedEEA InPlaceArithmetic

/-- The saved quotient is the physical A read of the actual forward native product. -/
def saved (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) : Fin (2 ^ modulus.size) :=
  accumulator modulus.size (NativeProductFrame.step modulus.size (modulusWord modulus)
    (InPlaceForward.result modulus value.val positive bounded, numerator))

/-- The complete output already established for the identical EEA adjoint on reused Y. -/
def recovered (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) : Frame modulus.size :=
  (WorkspaceReuse.placement modulus.size).grouping.symm
    (InitialPortProgram.inputFrame modulus value, saved modulus value numerator positive bounded)

/-- The saved physical word is the canonical finite residue of inverse X times Y. -/
lemma saved_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    (saved modulus value numerator positive bounded).val =
      ((CanonicalInverse.word modulus prime.pos value.val).val * numerator.val) % modulus :=
  product_quotient modulus prime value numerator positive bounded

private lemma recovered_input (modulus : Nat)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    input modulus.size (recovered modulus value numerator positive bounded) = value := by
  change input modulus.size ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.input_symm, initial_input]

private lemma recovered_numerator (modulus : Nat)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    ProductReadout.numerator modulus.size (recovered modulus value numerator positive bounded) =
      0 := by
  change ProductReadout.numerator modulus.size
    ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.numerator_symm, initial_accumulator]

private lemma recovered_accumulator (modulus : Nat)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    accumulator modulus.size (recovered modulus value numerator positive bounded) =
      saved modulus value numerator positive bounded := by
  change accumulator modulus.size ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.accumulator_symm, numerator_eq]

private lemma recomputed_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (value.val * (saved modulus value numerator positive bounded).val) % modulus =
      numerator.val := by
  let : NeZero modulus := ⟨prime.ne_zero⟩
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  have inverseBound : (CanonicalInverse.word modulus prime.pos value.val).val < modulus := by
    rw [← CanonicalInverse.source_eq_word modulus value.val coprime positive bounded]
    exact CanonicalInverse.source_lt modulus value.val coprime positive bounded
  have inverse := InverseOutput.word_product modulus value.val coprime positive bounded
  rw [CanonicalInverse.source_eq_word modulus value.val coprime positive bounded] at inverse
  have cancels : (value.val : ZMod modulus) *
      (((CanonicalInverse.word modulus prime.pos value.val).val : ZMod modulus) *
        (numerator.val : ZMod modulus)) = (numerator.val : ZMod modulus) := by
    rw [← mul_assoc, inverse, one_mul]
  have values := congrArg ZMod.val cancels
  rw [ZMod.val_mul, ZMod.val_mul, ZMod.val_natCast_of_lt bounded,
    ZMod.val_natCast_of_lt inverseBound, ZMod.val_natCast_of_lt numeratorBound] at values
  rw [← saved_value modulus prime value numerator positive bounded] at values
  exact values

/-- The actual recomputed Y is the original measured numerator, without a nonzero-Y restriction. -/
lemma recomputed_numerator (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (ReusedProduct.computeStep modulus.size (modulusWord modulus)
      (recovered modulus value numerator positive bounded)).2 = numerator := by
  have valid : (ProductReadout.numerator modulus.size
      (recovered modulus value numerator positive bounded)).val < (modulusWord modulus).val := by
    rw [recovered_numerator]
    exact prime.pos
  have actual := ReusedProductPortLaws.compute_numerator modulus.size (modulusWord modulus)
    (recovered modulus value numerator positive bounded) valid
  rw [recovered_numerator, recovered_input, recovered_accumulator, numerator_eq] at actual
  have nativeModulus : (modulusWord modulus).val = modulus := rfl
  have scalar : (ReusedProduct.computeStep modulus.size (modulusWord modulus)
      (recovered modulus value numerator positive bounded)).2.val =
        (value.val * (saved modulus value numerator positive bounded).val) % modulus := by
    simpa only [Fin.val_zero, Nat.zero_add, nativeModulus] using actual
  exact Fin.ext (scalar.trans
    (recomputed_value modulus prime value numerator positive bounded numeratorBound))

/-- Every other actual word, padding bit and history bit is retained during recomputation. -/
lemma compute_frame (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ReusedProduct.computeStep modulus.size (modulusWord modulus)
        (recovered modulus value numerator positive bounded) =
      ((recovered modulus value numerator positive bounded).1, numerator) := by
  let state := recovered modulus value numerator positive bounded
  apply ProductPortLaws.frame_ext
  · exact (ReusedProductPortLaws.compute_input modulus.size (modulusWord modulus) state).trans
      (input_pair modulus.size state.1 state.2 numerator)
  · rw [numerator_eq, numerator_eq]
    exact recomputed_numerator modulus prime value numerator positive bounded numeratorBound
  · exact (ReusedProductPortLaws.compute_accumulator modulus.size (modulusWord modulus) state).trans
      (accumulator_pair modulus.size state.1 state.2 numerator)
  · exact (ReusedProductPortLaws.compute_history modulus.size (modulusWord modulus) state).trans
      (history_pair modulus.size state.1 state.2 numerator)

/-- The complete frame equation is realized by the actual emitted X/A/Y product program. -/
lemma compute_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((ReusedProduct.compute modulus.size (modulusWord modulus)).applyNormalized environment)
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
              (recovered modulus value numerator positive bounded)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            ((recovered modulus value numerator positive bounded).1, numerator))) := by
  have actual := (ReusedProduct.reusedProduct_realizes (environment := environment) modulus.size
    (modulusWord modulus)).apply_encoded_ket (recovered modulus value numerator positive bounded)
  rw [compute_frame modulus prime value numerator positive bounded numeratorBound] at actual
  exact actual

/-- Actual selected Z gates and the identical product adjoint attach the original Y character. -/
lemma correction_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).applyVec environment)
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
              (recovered modulus value numerator positive bounded)))).vec =
      WalshHadamard.walshSign outcome numerator •
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
              (recovered modulus value numerator positive bounded)))).vec := by
  have actual := ReusedProduct.correction_ket (environment := environment) modulus.size (modulusWord
    modulus) outcome
    (recovered modulus value numerator positive bounded)
  rw [recomputed_numerator modulus prime value numerator positive bounded numeratorBound] at actual
  exact actual

/-- The actual unitary correction cancels the measured phase without changing any complete label. -/
lemma correction_cancels (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).applyVec environment)
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
              ((frameEncoding modulus.size).encode
                (recovered modulus value numerator positive bounded)))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (recovered modulus value numerator positive bounded)))).vec := by
  rw [UnitaryCircuit.applyVec_smul,
    correction_ket modulus prime value numerator outcome positive bounded numeratorBound,
    smul_smul, WalshHadamard.walshSign_mul_self, one_smul]

/-- The literal correction and final swap place the quotient in Y and restore the entire seed. -/
lemma correction_swap (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (((ReusedProduct.correction modulus.size (modulusWord modulus)
      (fun index => outcome.val.testBit index.val)).seq (FrameSwap.program modulus.size)).applyVec
        environment)
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
              ((frameEncoding modulus.size).encode
                (recovered modulus value numerator positive bounded)))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (InitialPortProgram.inputFrame modulus value,
              saved modulus value numerator positive bounded)))).vec := by
  rw [UnitaryCircuit.applyVec_seq,
    correction_cancels modulus prime value numerator outcome positive bounded numeratorBound]
  exact congrArg NormalizedVector.vec (FrameSwapReadout.program_reused_ket (environment :=
    environment) modulus.size
      (InitialPortProgram.inputFrame modulus value, saved modulus value numerator positive bounded))

end

end QuantumAlg.MeasuredUncompute.InPlaceRecompute
