/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Data.Fintype.Card

/-!
# Exact finite indexing of actual native random bit strings

The index is a proof-side label for the already generated bit string. It uses
the fixed most-significant-first storage convention and is bijective at every
width, including zero. It neither allocates a word nor replaces the sampler by
a second random draw or an uncounted arithmetic instruction.
-/

namespace QuantumAlg.BitWord.Random

noncomputable section

private def coordinates (width : Nat) : CShape.Value (.bits width) ≃ (Fin width → Fin 2) where
  toFun value := fun index => finTwoEquiv.symm (value.bitGet index).toBool
  invFun bits := .bits (fun index => finTwoEquiv (bits index))
  left_inv value := by
    cases value with
    | bits values =>
        apply congrArg CShape.Value.bits
        funext index
        exact finTwoEquiv.apply_symm_apply (values index)
  right_inv bits := by
    funext index
    exact finTwoEquiv.symm_apply_apply (bits index)

/-- Bijection between the actual native output values and the source finite sample labels. -/
public def sampleEquiv (width : Nat) : CShape.Value (.bits width) ≃ Fin (2 ^ width) := by
  exact (coordinates width).trans (BinaryBasis.bigEndianEquiv width)

/-- Decoding a sample index gives the exact existing most-significant-first stored bit. -/
public lemma randomSampleEquiv_symm_bit (width : Nat) (value : Fin (2 ^ width))
    (index : Fin width) :
    (((sampleEquiv width).symm value).bitGet index).toBool =
      value.val.testBit (width - 1 - index.val) := by
  change finTwoEquiv ((BinaryBasis.bigEndianEquiv width).symm value index) = _
  rw [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  congr 1
  change width - (index.val + 1) = width - 1 - index.val
  omega

/-- The native output carrier has exactly one value for each finite sample label. -/
public lemma randomBitsValue_card (width : Nat) :
    Fintype.card (CShape.Value (.bits width)) = 2 ^ width :=
  (Fintype.card_congr (sampleEquiv width)).trans (Fintype.card_fin _)

/-- Every actual bit-string value has the source uniform probability, including width zero. -/
public lemma randomUniformBits_apply (width : Nat) (value : CShape.Value (.bits width)) :
    uniformBits width value = ((2 ^ width : Nat) : ENNReal)⁻¹ := by
  rw [uniformBits, PMF.uniformOfFintype_apply, randomBitsValue_card]

/-- Finite sample indexing preserves the same uniform mass used by the original source. -/
public lemma randomUniformBits_sample (width : Nat) (value : Fin (2 ^ width)) :
    uniformBits width ((sampleEquiv width).symm value) = ((2 ^ width : Nat) : ENNReal)⁻¹ :=
  randomUniformBits_apply width _

end

end QuantumAlg.BitWord.Random
