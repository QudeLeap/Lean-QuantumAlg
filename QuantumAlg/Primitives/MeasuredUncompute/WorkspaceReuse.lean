/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

/-!
# Actual placement of shared arithmetic on the reset Y workspace

The inverse EEA reuses Y in the role previously occupied by A while X
and all small history coordinates keep their actual physical positions.
This is a placement of the actual supplied native program; no SWAP is
executed by the coordinate map itself. The separate final word SWAP is
an explicitly charged program [LYL+26, sec_point_add/sec_point_add.tex:75-105].
-/

namespace QuantumAlg.MeasuredUncompute.WorkspaceReuse

noncomputable section

open ProductPlacement MAU.Inversion

/-- Native A addresses are placed on Y and the complementary Y addresses on the original A. -/
def address (width index : Nat) : Nat :=
  if index < width then (SharedEEA.encoding width).width + index
  else if (SharedEEA.encoding width).width ≤ index then index - (SharedEEA.encoding width).width
  else index

private theorem address_bound (width : Nat) (index : Fin (frameEncoding width).width) :
    address width index.val < (frameEncoding width).width := by
  have bound := index.isLt
  have shared := SharedEEA.encoding_width width
  change index.val < (SharedEEA.encoding width).width + width at bound
  change _ < (SharedEEA.encoding width).width + width
  unfold address
  split_ifs <;> omega

private theorem address_twice (width : Nat) (index : Fin (frameEncoding width).width) :
    address width (address width index.val) = index.val := by
  have bound := index.isLt
  have shared := SharedEEA.encoding_width width
  change index.val < (SharedEEA.encoding width).width + width at bound
  unfold address
  split_ifs <;> omega

/-- Every actual large-word and history wire has a unique corresponding source role. -/
def wires (width : Nat) : Equiv.Perm (Fin (frameEncoding width).width) where
  toFun index := ⟨address width index.val, address_bound width index⟩
  invFun index := ⟨address width index.val, address_bound width index⟩
  left_inv index := Fin.ext (address_twice width index)
  right_inv index := Fin.ext (address_twice width index)

/-- Place the same existing full native program on the proved reused physical coordinates. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (frameEncoding width) (frameEncoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (frame_total width) (frame_total width) (wires width)

/-- Each original large-workspace address now names precisely the corresponding reset Y wire. -/
theorem address_accumulator (width : Nat) (index : Fin width) :
    address width index.val = (SharedEEA.encoding width).width + index.val :=
  if_pos index.isLt

/-- Complementary Y roles retain their old data at the corresponding original A positions. -/
theorem address_numerator (width : Nat) (index : Fin width) :
    address width ((SharedEEA.encoding width).width + index.val) = index.val := by
  have shared := SharedEEA.encoding_width width
  unfold address
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- X, the six padding positions and every small EEA field keep their original physical identity. -/
theorem address_retained (width index : Nat)
    (afterAccumulator : width ≤ index)
    (beforeNumerator : index < (SharedEEA.encoding width).width) :
    address width index = index := by
  unfold address
  rw [if_neg (by omega), if_neg (by omega)]

end

end QuantumAlg.MeasuredUncompute.WorkspaceReuse
