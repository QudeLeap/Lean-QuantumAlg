/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow.BitReverse
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Actual source tuple coordinates

The existing source binary labels decode to their recursive physical head and
tail bits in MSB-first order. These are mathematical basis coordinates, without
a classical packing operation or a quantum wire permutation.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

/-- Existing source binary coordinates of a recursive physical bit tuple. -/
def tupleCoordinates (n : Nat) (outcome : Bits n) : Fin n → Fin 2 :=
  (BinaryBasis.bigEndianEquiv n).symm (binaryEquiv n outcome)

/-- No physical bit is lost by the source's tuple coordinates. -/
lemma tupleCoordinates_injective (n : Nat) : Function.Injective (tupleCoordinates n) :=
  (BinaryBasis.bigEndianEquiv n).symm.injective.comp (binaryEquiv n).injective

/-- The source tuple's leading coordinate is the actual physical head bit. -/
lemma tupleCoordinates_head (n : Nat) (head : Fin 2) (tail : Bits n) :
    tupleCoordinates (n + 1) (head, tail) 0 = head := by
  change finTwoEquiv.symm
    ((qftPairEquiv n (head, binaryEquiv n tail)).val.testBit
      (Fin.rev (0 : Fin (n + 1))).val) = head
  have position : (Fin.rev (0 : Fin (n + 1))).val = n := by
    simp only [Fin.val_rev, Fin.val_zero]
    omega
  rw [position, qftPairEquiv_testBit_high]
  fin_cases head <;> rfl

/-- Dropping the physical head retains exactly the existing source tail tuple. -/
lemma tupleCoordinates_tail (n : Nat) (head : Fin 2) (tail : Bits n)
    (index : Fin n) :
    tupleCoordinates (n + 1) (head, tail) index.succ =
      tupleCoordinates n tail index := by
  change finTwoEquiv.symm
    ((qftPairEquiv n (head, binaryEquiv n tail)).val.testBit index.succ.rev.val) =
      finTwoEquiv.symm ((binaryEquiv n tail).val.testBit index.rev.val)
  have position : index.succ.rev.val = index.rev.val := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  rw [position, qftPairEquiv_testBit_low]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
