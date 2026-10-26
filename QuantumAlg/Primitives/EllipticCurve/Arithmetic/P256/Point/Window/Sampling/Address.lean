/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Stream
import all QuantumAlg.Util.Nat.FixedWidth.Radix

/-!
# The actual source partition selects the same original unsigned window digit

Every current source bit has its original exponent coordinate. The complete
sixteen-bit windows and the high four-bit tail therefore select the exact
radix digit of the same full 260-bit pair. These mathematical coordinates do
not change the physical source feed, ports, references or instruction order.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical.Window.Source

/-- The original exponent of the current stream, retaining its complete unsigned range. -/
def sourceValue (index : WindowIndex) (branch : SourceRegister.Index) : Fin (2 ^ 260) :=
  if index.stream.val = 0 then branch.1 else branch.2

private lemma source_digit_bound (index : WindowIndex) (value : Fin (2 ^ 260)) :
    Nat.FixedWidth.Radix.digit (2 ^ 16) value.val index.logical.val <
      2 ^ (index.lowerWidth + 1) := by
  by_cases full : index.full
  · simpa only [Nat.FixedWidth.Radix.digit, WindowIndex.lowerWidth, if_pos full] using
      Nat.mod_lt (value.val / (2 ^ 16) ^ index.logical.val) (Nat.two_pow_pos 16)
  · have last : index.logical.val = 16 := by
      have within := index.logical.isLt
      change ¬index.logical.val < 16 at full
      omega
    have bounded := Nat.FixedWidth.Radix.binary_tail_digit_lt_of_width
      (width := 260) (chunk := 16) (window := 16) (tailWidth := 4) (by decide) value.isLt
    simpa only [WindowIndex.lowerWidth, if_neg full, last] using bounded

/-- The complete current digit, including its top address bit and the lower address bits. -/
def sourceDigit (index : WindowIndex) (branch : SourceRegister.Index) :
    (Qubits (index.lowerWidth + 1)).Index :=
  ⟨Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceValue index branch).val index.logical.val,
    source_digit_bound index (sourceValue index branch)⟩

private lemma source_index_coordinate (index : WindowIndex)
    (bit : Fin (index.lowerWidth + 1)) :
    260 - (index.start + bit.val + 1) = 16 * index.logical.val + bit.rev.val := by
  have reversed : bit.rev.val = index.lowerWidth + 1 - (bit.val + 1) := Fin.val_rev bit
  by_cases full : index.full
  · have width : index.lowerWidth = 15 := if_pos full
    have logicalBound : index.logical.val < 16 := full
    have bitBound : bit.val < 16 := by
      simpa only [WindowIndex.lowerWidth, if_pos full] using bit.isLt
    simp only [WindowIndex.start, if_pos full]
    omega
  · have width : index.lowerWidth = 3 := if_neg full
    have last : index.logical.val = 16 := by
      have within := index.logical.isLt
      change ¬index.logical.val < 16 at full
      omega
    have bitBound : bit.val < 4 := by
      simpa only [WindowIndex.lowerWidth, if_neg full] using bit.isLt
    simp only [WindowIndex.start, if_neg full, last]
    omega

variable {ctx : RuntimeCtx .quantum}

namespace Parameters

/-- Each actual port bit has the original little-endian coordinate of this same logical row. -/
lemma sampling_sourceBit_logical (parameters : Parameters ctx) (index : WindowIndex)
    (bit : Fin (index.lowerWidth + 1)) :
    ((parameters.ports index).sourceBit bit).val = 16 * index.logical.val + bit.rev.val :=
  source_index_coordinate index bit

/-- The real feed's selected source label is precisely this original finite radix digit. -/
lemma sampling_sourcePartition_digit (parameters : Parameters ctx) (index : WindowIndex)
    (branch : SourceRegister.Index) :
    (parameters.sourcePartition index branch).1 = sourceDigit index branch := by
  apply (BinaryBasis.bigEndianEquiv (index.lowerWidth + 1)).symm.injective
  funext bit
  have selected := window_sourcePartition_stream (parameters.ports index) branch.1 branch.2 bit
  change (BinaryBasis.bigEndianEquiv (index.lowerWidth + 1)).symm
      (parameters.sourcePartition index branch).1 bit =
    finTwoEquiv.symm ((sourceValue index branch).val.testBit
      ((parameters.ports index).sourceBit bit).val) at selected
  refine selected.trans ?_
  rw [BinaryBasis.bigEndianEquiv_symm_value]
  apply congrArg finTwoEquiv.symm
  change (sourceValue index branch).val.testBit
      ((parameters.ports index).sourceBit bit).val =
    (Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceValue index branch).val
      index.logical.val).testBit bit.rev.val
  rw [parameters.sampling_sourceBit_logical]
  have bitBound : bit.rev.val < 16 :=
    bit.rev.isLt.trans_le (Nat.add_le_add_right index.lowerWidth_bound 1)
  exact (Nat.FixedWidth.Radix.binary_digit_bit 16 (sourceValue index branch).val
    index.logical.val ⟨bit.rev.val, bitBound⟩).symm

/-- No truncation to the subgroup order occurs in the actual source digit. -/
lemma sampling_sourcePartition_digit_val (parameters : Parameters ctx) (index : WindowIndex)
    (branch : SourceRegister.Index) :
    (parameters.sourcePartition index branch).1.val =
      Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceValue index branch).val index.logical.val :=
  congrArg Fin.val (parameters.sampling_sourcePartition_digit index branch)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
