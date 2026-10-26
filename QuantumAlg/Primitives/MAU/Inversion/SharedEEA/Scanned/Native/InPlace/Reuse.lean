/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Copy
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.WireBit
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Actual placement of shared arithmetic on the reset Y workspace

The inverse EEA reuses the physically reset numerator in the role
previously occupied by the large Work1 port. The input, all small source
history and every scan-pool wire keep their actual physical positions.
This is a placement of the actual supplied native program; no SWAP is
executed by the coordinate map itself. The separate final word SWAP is
an explicitly charged program [LYL+26, sec_point_add/sec_point_add.tex:75-105].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse

noncomputable section

open EncodedBit

private lemma frame_total (width : Nat) :
    Function.Surjective (OutputCopy.encoding width).encode :=
  Scanned.product_total _ _ (Scanned.encoding_surjective width) Function.surjective_id

/-- Native A addresses are placed on Y and the complementary Y addresses on the original A. -/
def address (width index : Nat) : Nat :=
  if index < width then (Scanned.encoding width).width + index
  else if (Scanned.encoding width).width ≤ index then index - (Scanned.encoding width).width
  else index

private lemma address_bound (width : Nat) (index : Fin (OutputCopy.encoding width).width) :
    address width index.val < (OutputCopy.encoding width).width := by
  have bound := index.isLt
  have shared := Scanned.encoding_width width
  change index.val < (Scanned.encoding width).width + width at bound
  change _ < (Scanned.encoding width).width + width
  unfold address
  split_ifs <;> omega

private lemma address_twice (width : Nat) (index : Fin (OutputCopy.encoding width).width) :
    address width (address width index.val) = index.val := by
  have bound := index.isLt
  have shared := Scanned.encoding_width width
  change index.val < (Scanned.encoding width).width + width at bound
  unfold address
  split_ifs <;> omega

/-- Every actual large-word and history/pool wire has a unique corresponding source role. -/
def wires (width : Nat) : Equiv.Perm (Fin (OutputCopy.encoding width).width) where
  toFun index := ⟨address width index.val, address_bound width index⟩
  invFun index := ⟨address width index.val, address_bound width index⟩
  left_inv index := Fin.ext (address_twice width index)
  right_inv index := Fin.ext (address_twice width index)

/-- Place the same existing full native program on the proved reused physical coordinates. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (OutputCopy.encoding width) (OutputCopy.encoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (frame_total width) (frame_total width) (wires width)

/-- Each original large-workspace address now names precisely the corresponding reset Y wire. -/
lemma address_accumulator (width : Nat) (index : Fin width) :
    address width index.val = (Scanned.encoding width).width + index.val :=
  if_pos index.isLt

/-- Complementary Y roles retain their old data at the corresponding original A positions. -/
lemma address_numerator (width : Nat) (index : Fin width) :
    address width ((Scanned.encoding width).width + index.val) = index.val := by
  have shared := Scanned.encoding_width width
  unfold address
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- X, padding, all small history and the pool retain their physical identities. -/
lemma address_retained (width index : Nat)
    (afterAccumulator : width ≤ index)
    (beforeNumerator : index < (Scanned.encoding width).width) :
    address width index = index := by
  unfold address
  rw [if_neg (by omega), if_neg (by omega)]

/-- Every actual appended address, prefix and conjunction wire keeps exactly its old position. -/
lemma address_pool (width : Nat) (index : Fin (poolEncoding width).width) :
    address width ((SharedEEA.encoding width).width + index.val) =
      (SharedEEA.encoding width).width + index.val := by
  apply address_retained
  · rw [SharedEEA.encoding_width]
    omega
  · change (SharedEEA.encoding width).width + index.val <
      (SharedEEA.encoding width).width + (poolEncoding width).width
    omega

private lemma pool_total (width : Nat) : Function.Surjective (poolEncoding width).encode :=
  Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective
    (Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective Scanned.bool_total)

/-- The full physical reuse grouping reads exactly the same entire original scan pool. -/
lemma grouping_pool (width : Nat) (state : OutputCopy.Data width) :
    ((placement width).grouping state).1.2 = state.1.2 := by
  apply state_eq_of_get_eq (pool_total width)
  intro bit
  let observed : EncodedBit (OutputCopy.encoding width) :=
    BinaryLabelEncoding.prodLeftBit (Scanned.encoding width)
      (BinaryLabelEncoding.finIdentity width)
      (BinaryLabelEncoding.prodRightBit (SharedEEA.encoding width) (poolEncoding width) bit)
  have location : ((placement width).placeBit observed).wire = observed.wire := by
    rw [placement, FullPlacement.ofWires_placeBit_wire]
    apply Fin.ext
    change address width ((SharedEEA.encoding width).width + bit.wire.val) =
      (SharedEEA.encoding width).width + bit.wire.val
    exact address_pool width bit.wire
  have same := EncodedBit.eq_of_wire_eq _ _ location
  have read := congrArg (fun lens : EncodedBit (OutputCopy.encoding width) => lens.get state) same
  exact read

/-- Reassembling the physically reused source also returns the identical entire pool. -/
lemma grouping_symm_pool (width : Nat) (state : OutputCopy.Data width) :
    ((placement width).grouping.symm state).1.2 = state.1.2 := by
  have actual := grouping_pool width ((placement width).grouping.symm state)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse
