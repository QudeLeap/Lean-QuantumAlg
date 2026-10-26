/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition

/-!
# The same paired mathematical source labels supply every real window

The first source label precedes the second in the mathematical product.
Chronological coordinates select their original most-significant-first
positions, hence their original little-endian exponent bits. The source
partition is mathematical only and does not add any physical systems.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

/-- Select the current stream's original positions in one paired mathematical source. -/
def streamPositions (ports : Ports ctx totalBits active) : Fin active ↪ Fin (totalBits + totalBits)
    where
  toFun index := if ports.stream.val = 0 then (ports.position index).castAdd totalBits
    else (ports.position index).natAdd totalBits
  inj' first second same := by
    have values := congrArg Fin.val same
    apply Fin.ext
    by_cases stream : ports.stream.val = 0
    · simp only [if_pos stream] at values
      change ports.start + first.val = ports.start + second.val at values
      omega
    · simp only [if_neg stream] at values
      change totalBits + (ports.start + first.val) =
        totalBits + (ports.start + second.val) at values
      omega

/-- The same original exponent pair, with no frequency reversal or runtime packing. -/
def pairedSource (first second : Fin (2 ^ totalBits)) : (Qubits (totalBits + totalBits)).Index :=
  prodEquiv (first, second)

/-- Every block reads exactly its own exponent's original bits at the real chronological offset. -/
lemma window_sourcePartition_stream (ports : Ports ctx totalBits active)
    (first second : Fin (2 ^ totalBits)) (index : Fin active) :
    (BinaryBasis.bigEndianEquiv active).symm
        (labelPartition (streamPositions ports) (pairedSource first second)).1 index =
      finTwoEquiv.symm
        ((if ports.stream.val = 0 then first else second).val.testBit
          (ports.sourceBit index).val) := by
  rw [window_sourcePartition_coordinate]
  by_cases stream : ports.stream.val = 0
  · have position : (streamPositions ports index).rev.val =
        totalBits + (ports.sourceBit index).val := by
      have chosen : streamPositions ports index = (ports.position index).castAdd totalBits := by
        change (if ports.stream.val = 0 then (ports.position index).castAdd totalBits
          else (ports.position index).natAdd totalBits) = _
        rw [if_pos stream]
      rw [chosen]
      simp only [Fin.val_rev, Fin.val_castAdd, Ports.sourceBit]
      have within := (ports.position index).isLt
      omega
    rw [position, if_pos stream]
    exact congrArg finTwoEquiv.symm (prodEquiv_testBit_left first second _)
  · have position : (streamPositions ports index).rev.val = (ports.sourceBit index).val := by
      have chosen : streamPositions ports index = (ports.position index).natAdd totalBits := by
        change (if ports.stream.val = 0 then (ports.position index).castAdd totalBits
          else (ports.position index).natAdd totalBits) = _
        rw [if_neg stream]
      rw [chosen]
      simp only [Fin.val_rev, Fin.val_natAdd, Ports.sourceBit]
      omega
    rw [position, if_neg stream]
    exact congrArg finTwoEquiv.symm (prodEquiv_testBit_right first second _)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
