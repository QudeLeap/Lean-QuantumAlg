/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small

/-!
# Zero-, one- and two-bit bi-flip instructions

At these fixed base widths, the bi-flip `pivot - 1 - input` modulo the word
capacity is affine over bits. The following X/CNOT lists implement it without
a borrowed bit [G17, paper.tex:276-277]. General widths use the recursive
arithmetic construction.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Small

noncomputable section

open BinaryLabelEncoding EncodedBit.GateSpec Nat.FixedWidth

private def oneBit : EncodedBit (finIdentity 1) := finIdentityBit 1 0
private def highBit : EncodedBit (finIdentity 2) := finIdentityBit 2 0
private def lowBit : EncodedBit (finIdentity 2) := finIdentityBit 2 1

private def oneBiFlip (pivot : Fin (2 ^ 1 + 1)) :
    List (EncodedBit.GateSpec (finIdentity 1)) :=
  if pivot.val = 1 then [] else [.x oneBit]

private def twoBiFlip (pivot : Fin (2 ^ 2 + 1)) :
    List (EncodedBit.GateSpec (finIdentity 2)) :=
  match pivot.val with
  | 1 => [.cnot lowBit highBit (by decide)]
  | 2 => [.x lowBit]
  | 3 => [.cnot lowBit highBit (by decide), .x highBit]
  | _ => [.x lowBit, .x highBit]

/-- The exact small-width bi-flip emits at most two X/CNOT instructions. -/
def biFlipGates : (width : Nat) → width ≤ 2 → Fin (2 ^ width + 1) →
    List (EncodedBit.GateSpec (finIdentity width))
  | 0, _, _ => []
  | 1, _, pivot => oneBiFlip pivot
  | 2, _, pivot => twoBiFlip pivot
  | width + 3, impossible, _ => False.elim (by omega)

/-- Every base-width input has the exact bi-flip value. -/
theorem biFlipGates_step (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) (input : Fin (2 ^ width)) :
    stepList (biFlipGates width small pivot) input = biFlipWordOutput pivot input := by
  interval_cases width <;> fin_cases pivot <;> fin_cases input <;> rfl

/-- The explicit finite base lists contain at most two instructions. -/
theorem biFlipGates_length (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) : (biFlipGates width small pivot).length ≤ 2 := by
  interval_cases width <;> fin_cases pivot <;> dsimp only [biFlipGates] <;> decide

end

end QuantumAlg.MAU.Addition.Gidney.Small
