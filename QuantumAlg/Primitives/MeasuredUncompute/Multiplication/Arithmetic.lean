/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic
import all QuantumAlg.Primitives.MeasuredUncompute.Native.ReusedEEA
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.PortLaws

/-!
# Actual product and inverse-workspace frames for measured multiplication

The first actual product saves X*Y in A, including product zero. Resetting
old Y supplies exactly the existing shared EEA's required large workspace.
Its actual forward then exposes X-inverse while retaining saved A and the
entire history [LYL+26, sec_point_add/sec_point_add.tex:32-36,119-122].

The arithmetic cancellation uses only the original nonzero X and canonical
Y domain. No inverse of Y or of the saved product is needed. The surrounding
measurement proof supplies the actual reset label and Walsh amplitude.
-/

namespace QuantumAlg.MeasuredUncompute.MultiplicationArithmetic

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ProductPlacement ProductReadout MAU.Inversion SharedEEA
open NumberTheory.SharedEEA InPlaceArithmetic

/-- Saved A is read from the actual initial native product, not specified by a separate oracle. -/
def saved (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  accumulator modulus.size (NativeProductFrame.step modulus.size (modulusWord modulus)
    (InitialPortProgram.inputFrame modulus value, numerator))

/-- The actual product's complete reset frame, with Y used as the large EEA workspace. -/
def resetFrame (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) : Frame modulus.size :=
  (WorkspaceReuse.placement modulus.size).grouping.symm
    (InitialPortProgram.inputFrame modulus value, saved modulus value numerator)

/-- The actual reused forward result retains the complete saved product and all small history. -/
def inverseFrame (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) : Frame modulus.size :=
  (WorkspaceReuse.placement modulus.size).grouping.symm
    (InPlaceForward.result modulus value.val positive bounded, saved modulus value numerator)

/-- The independent arithmetic value follows from the actual native accumulation at clean A. -/
lemma saved_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size)) :
    (saved modulus value numerator).val = (value.val * numerator.val) % modulus := by
  have valid : (accumulator modulus.size
      (InitialPortProgram.inputFrame modulus value, numerator)).val <
        (modulusWord modulus).val := by
    rw [initial_accumulator]
    exact prime.pos
  have actual := ProductPortLaws.step_accumulator modulus.size (modulusWord modulus)
    (InitialPortProgram.inputFrame modulus value, numerator) valid
  rw [initial_accumulator, initial_input, numerator_eq] at actual
  have nativeModulus : (modulusWord modulus).val = modulus := rfl
  change (accumulator modulus.size (NativeProductFrame.step modulus.size (modulusWord modulus)
    (InitialPortProgram.inputFrame modulus value, numerator))).val = _
  simpa only [Fin.val_zero, Nat.zero_add, nativeModulus] using actual

/-- The actual product followed by a reset label has exactly the full reused-forward input. -/
lemma reset_frame (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus)
      (InitialPortProgram.inputFrame modulus value, numerator)
    (multiplied.1, 0) = resetFrame modulus value numerator :=
  zero_accumulator_reset modulus.size (modulusWord modulus) _ numerator
    (initial_accumulator modulus value numerator)

/-- The existing reused native EEA maps the complete reset frame to its exact inverse frame. -/
lemma forward_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    ((NativeReusedEEA.forward modulus prime).applyNormalized environment)
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (resetFrame modulus value numerator)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (inverseFrame modulus value numerator positive bounded))) :=
  NativeReusedEEA.forward_initial modulus prime value (saved modulus value numerator)
    positive bounded

private lemma inverse_input (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    input modulus.size (inverseFrame modulus value numerator positive bounded) =
      CanonicalInverse.word modulus prime.pos value.val := by
  change input modulus.size ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.input_symm, forward_input modulus prime]

private lemma inverse_numerator (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    ProductReadout.numerator modulus.size (inverseFrame modulus value numerator positive bounded) =
      0 := by
  change ProductReadout.numerator modulus.size
    ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.numerator_symm, forward_accumulator modulus prime]

private lemma inverse_accumulator (modulus : Nat)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus) :
    accumulator modulus.size (inverseFrame modulus value numerator positive bounded) =
      saved modulus value numerator := by
  change accumulator modulus.size ((WorkspaceReuse.placement modulus.size).grouping.symm _) = _
  rw [ReusedProductReadout.accumulator_symm, numerator_eq]

/-- Inverse X times saved X*Y is the original Y, including Y=0 on the full original domain. -/
lemma recomputed_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((CanonicalInverse.word modulus prime.pos value.val).val *
      (saved modulus value numerator).val) % modulus = numerator.val := by
  let : NeZero modulus := ⟨prime.ne_zero⟩
  have coprime := (Nat.coprime_of_lt_prime (Nat.ne_of_gt positive) bounded prime).symm
  have inverseBound : (CanonicalInverse.word modulus prime.pos value.val).val < modulus := by
    rw [← CanonicalInverse.source_eq_word modulus value.val coprime positive bounded]
    exact CanonicalInverse.source_lt modulus value.val coprime positive bounded
  have inverse := InverseOutput.word_product modulus value.val coprime positive bounded
  rw [CanonicalInverse.source_eq_word modulus value.val coprime positive bounded] at inverse
  have reverseInverse : ((CanonicalInverse.word modulus prime.pos value.val).val : ZMod modulus) *
      (value.val : ZMod modulus) = 1 := by
    rw [mul_comm]
    exact inverse
  have cancels : ((CanonicalInverse.word modulus prime.pos value.val).val : ZMod modulus) *
      ((value.val : ZMod modulus) * (numerator.val : ZMod modulus)) =
        (numerator.val : ZMod modulus) := by
    rw [← mul_assoc, reverseInverse, one_mul]
  have values := congrArg ZMod.val cancels
  rw [ZMod.val_mul, ZMod.val_mul, ZMod.val_natCast_of_lt bounded,
    ZMod.val_natCast_of_lt inverseBound, ZMod.val_natCast_of_lt numeratorBound] at values
  rw [← saved_value modulus prime value numerator] at values
  exact values

/-- The actual X/A/Y recomputation writes precisely the original measured Y label. -/
lemma recomputed_numerator (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (ReusedProduct.computeStep modulus.size (modulusWord modulus)
      (inverseFrame modulus value numerator positive bounded)).2 = numerator := by
  have valid : (ProductReadout.numerator modulus.size
      (inverseFrame modulus value numerator positive bounded)).val < (modulusWord modulus).val := by
    rw [inverse_numerator modulus prime]
    exact prime.pos
  have actual := ReusedProductPortLaws.compute_numerator modulus.size (modulusWord modulus)
    (inverseFrame modulus value numerator positive bounded) valid
  rw [inverse_numerator modulus prime, inverse_input modulus prime,
    inverse_accumulator, numerator_eq] at actual
  have nativeModulus : (modulusWord modulus).val = modulus := rfl
  have scalar : (ReusedProduct.computeStep modulus.size (modulusWord modulus)
      (inverseFrame modulus value numerator positive bounded)).2.val =
        ((CanonicalInverse.word modulus prime.pos value.val).val *
          (saved modulus value numerator).val) % modulus := by
    simpa only [Fin.val_zero, Nat.zero_add, nativeModulus] using actual
  exact Fin.ext (scalar.trans
    (recomputed_value modulus prime value numerator positive bounded numeratorBound))

end

end QuantumAlg.MeasuredUncompute.MultiplicationArithmetic
