/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Exponents
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact original branch coordinates for the complete exponent register

The original pair of finite exponent labels is equivalent to the actual
runtime basis. This equivalence composes the established big-endian product
and binary basis maps with the actual indexed-system correspondence. It
agrees exactly with the original paired selection function, including width
zero, so every original branch is retained once and every runtime basis value
is covered. Coherent states can use this bijection without discarding branches.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

private lemma bool_encode_finTwoEquiv (value : Bool) :
    finTwoEquiv (BinaryLabelEncoding.bool.encode value) = value := by
  cases value <;> rfl

private lemma pairedBranch_bit (exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (index : Fin (2 * exponentWidth)) :
    (prodEquiv branch).val.testBit index.rev.val =
      ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index := by
  unfold ExceptionalOffsetAveraging.pairedBigEndianSelected
  split_ifs with first
  · have localLt : exponentWidth - 1 - index.val < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth + (exponentWidth - 1 - index.val) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_left branch.1 branch.2
      (⟨exponentWidth - 1 - index.val, localLt⟩ : Fin exponentWidth)
  · have localLt : exponentWidth - 1 - (index.val - exponentWidth) < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth - 1 - (index.val - exponentWidth) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_right branch.1 branch.2
      (⟨exponentWidth - 1 - (index.val - exponentWidth), localLt⟩ : Fin exponentWidth)

/-- Original exponent pairs and the actual complete exponent basis are in exact correspondence. -/
def pairedExponentEquiv (modulus exponentWidth : Nat) :
    (Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) ≃
      (exponents modulus.size (2 * exponentWidth)).register.Index :=
  (prodEquiv (m := exponentWidth) (n := exponentWidth)).trans
    ((finCongr (congrArg (fun width : Nat => 2 ^ width)
      (show exponentWidth + exponentWidth = 2 * exponentWidth by omega))).trans
      ((BinaryBasis.bigEndianEquiv (2 * exponentWidth)).symm.trans
        (rangeBasis modulus.size (2 * exponentWidth)).symm))

/-- The established product and binary maps give precisely the original paired physical input. -/
lemma pairedExponentEquiv_apply (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    pairedExponentEquiv modulus exponentWidth branch =
      pairedExponentInput modulus exponentWidth branch := by
  apply (rangeBasis modulus.size (2 * exponentWidth)).injective
  rw [pairedExponentInput_rangeBasis]
  funext index
  change (BinaryBasis.bigEndianEquiv (2 * exponentWidth)).symm
      (finCongr (congrArg (fun width : Nat => 2 ^ width)
        (show exponentWidth + exponentWidth = 2 * exponentWidth by omega))
          (prodEquiv branch)) index =
    BinaryLabelEncoding.bool.encode
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index)
  rw [BinaryBasis.bigEndianEquiv_symm_value]
  apply finTwoEquiv.injective
  rw [Equiv.apply_symm_apply, bool_encode_finTwoEquiv]
  exact pairedBranch_bit exponentWidth branch index

/-- Decoding the actual paired input recovers the complete original exponent pair. -/
lemma pairedExponentEquiv_symm_input (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (pairedExponentEquiv modulus exponentWidth).symm
      (pairedExponentInput modulus exponentWidth branch) = branch := by
  rw [← pairedExponentEquiv_apply]
  exact (pairedExponentEquiv modulus exponentWidth).symm_apply_apply branch

/-- The supplied paired exponent input never identifies distinct original branches. -/
lemma pairedExponentInput_injective (modulus exponentWidth : Nat) :
    Function.Injective (pairedExponentInput modulus exponentWidth) := by
  intro left right same
  apply (pairedExponentEquiv modulus exponentWidth).injective
  simpa only [pairedExponentEquiv_apply] using same

/-- Every actual exponent basis value arises from an original pair, including width zero. -/
lemma pairedExponentInput_surjective (modulus exponentWidth : Nat) :
    Function.Surjective (pairedExponentInput modulus exponentWidth) := by
  intro value
  obtain ⟨branch, same⟩ := (pairedExponentEquiv modulus exponentWidth).surjective value
  exact ⟨branch, (pairedExponentEquiv_apply modulus exponentWidth branch).symm.trans same⟩

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
