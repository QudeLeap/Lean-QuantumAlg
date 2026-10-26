/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Move

/-!
# Existing binary address and unary output frame

Address positions here are least significant first. The original output
positions are divided into successively doubled ranges; no new quantum
system or address copy is allocated by the unary construction.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Existing low address and the existing clean range used as its unary output. -/
structure UnaryFrame (encoding : BinaryLabelEncoding Data) (width : Nat) where
  address : Fin width → EncodedBit encoding
  target : Fin (2 ^ width) → EncodedBit encoding
  addressDistinct : Function.Injective (fun index => (address index).wire)
  targetDistinct : Function.Injective (fun index => (target index).wire)
  outside : ∀ bit index, (address bit).wire ≠ (target index).wire

namespace UnaryFrame

private def oldIndex (depth : Nat) (present : depth < width) (index : Fin (2 ^ depth)) :
    Fin (2 ^ width) :=
  ⟨index.val, lt_of_lt_of_le index.isLt
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt present))⟩

private def freshIndex (depth : Nat) (present : depth < width) (index : Fin (2 ^ depth)) :
    Fin (2 ^ width) :=
  ⟨2 ^ depth + index.val, by
    have limit := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_of_lt present)
    rw [pow_succ] at limit
    have bound := index.isLt
    omega⟩

/-- Every unary stage uses the original address bit and two disjoint original output ranges. -/
def stage (frame : UnaryFrame encoding width) (depth : Nat) (present : depth < width) :
    UnaryMoveFrame encoding (2 ^ depth) where
  control := frame.address ⟨depth, present⟩
  old := ⟨fun index => frame.target (oldIndex depth present index)⟩
  fresh := ⟨fun index => frame.target (freshIndex depth present index)⟩
  oldDistinct := by
    intro first second equal
    have values := congrArg (fun index : Fin (2 ^ width) => index.val)
      (frame.targetDistinct equal)
    exact Fin.ext values
  freshDistinct := by
    intro first second equal
    have values := congrArg Fin.val (frame.targetDistinct equal)
    apply Fin.ext
    dsimp only [freshIndex, Fin.val_mk] at values
    omega
  separate := by
    intro first second equal
    have values := congrArg Fin.val (frame.targetDistinct equal)
    dsimp only [oldIndex, freshIndex, Fin.val_mk] at values
    have firstBound := first.isLt
    omega
  controlOld := fun _ => frame.outside _ _
  controlFresh := fun _ => frame.outside _ _

/-- Exactly one original unary output position is set; all other output positions are zero. -/
def OneHot (frame : UnaryFrame encoding width) (label : Fin (2 ^ width)) (state : Data) : Prop :=
  ∀ index, (frame.target index).get state = decide (index = label)

/-- An address-controlled stage moves the original selected index into the corresponding half. -/
def nextLabel (depth : Nat) (present : depth < width) (label : Fin (2 ^ width))
    (before : label.val < 2 ^ depth) (chosen : Bool) : Fin (2 ^ width) :=
  if chosen then freshIndex depth present ⟨label.val, before⟩ else label

private lemma stage_fresh_clean (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (label : Fin (2 ^ width)) (before : label.val < 2 ^ depth)
    (state : Data) (oneHot : frame.OneHot label state) (index : Fin (2 ^ depth)) :
    ((frame.stage depth present).fresh.bit index).get state = false := by
  change (frame.target (freshIndex depth present index)).get state = false
  rw [oneHot]
  apply decide_eq_false
  intro same
  have values := congrArg Fin.val same
  dsimp only [freshIndex, Fin.val_mk] at values
  omega

/-- The old prefix keeps its one-hot entry exactly on the unselected control branch. -/
lemma stage_get_old (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (label : Fin (2 ^ width)) (before : label.val < 2 ^ depth)
    (state : Data) (oneHot : frame.OneHot label state) (index : Fin (2 ^ depth)) :
    (frame.target (oldIndex depth present index)).get ((frame.stage depth present).step state) =
      (decide ((oldIndex depth present index) = label) &&
        !(frame.address ⟨depth, present⟩).get state) := by
  exact ((frame.stage depth present).old_get index state
    (frame.stage_fresh_clean depth present label before state oneHot index)).trans
      (by
        change ((frame.target (oldIndex depth present index)).get state &&
          !(frame.address ⟨depth, present⟩).get state) = _
        rw [oneHot])

/-- The new half receives the original one-hot entry exactly on the selected control branch. -/
lemma stage_get_fresh (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (label : Fin (2 ^ width)) (before : label.val < 2 ^ depth)
    (state : Data) (oneHot : frame.OneHot label state) (index : Fin (2 ^ depth)) :
    (frame.target (freshIndex depth present index)).get ((frame.stage depth present).step state) =
      ((frame.address ⟨depth, present⟩).get state &&
        decide ((oldIndex depth present index) = label)) := by
  exact ((frame.stage depth present).fresh_get index state
    (frame.stage_fresh_clean depth present label before state oneHot index)).trans
      (by
        change ((frame.address ⟨depth, present⟩).get state &&
          (frame.target (oldIndex depth present index)).get state) = _
        rw [oneHot])

/-- Original target positions beyond the doubled range retain their exact original values. -/
lemma stage_get_after (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (index : Fin (2 ^ width)) (after : 2 * 2 ^ depth ≤ index.val)
    (state : Data) :
    (frame.target index).get ((frame.stage depth present).step state) =
      (frame.target index).get state := by
  apply (frame.stage depth present).observed_get
  · intro other equal
    have values := congrArg Fin.val (frame.targetDistinct equal)
    dsimp only [stage, oldIndex, Fin.val_mk] at values
    have bound := other.isLt
    omega
  · intro other equal
    have values := congrArg Fin.val (frame.targetDistinct equal)
    dsimp only [stage, freshIndex, Fin.val_mk] at values
    have bound := other.isLt
    omega

/-- Every original address field is preserved by the same actual unary stage. -/
lemma stage_address (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (bit : Fin width) (state : Data) :
    (frame.address bit).get ((frame.stage depth present).step state) =
      (frame.address bit).get state :=
  (frame.stage depth present).observed_get _
    (fun _ => Ne.symm (frame.outside bit _)) (fun _ => Ne.symm (frame.outside bit _)) state

end UnaryFrame

end

end QuantumAlg.EncodedBit.WindowLookup
