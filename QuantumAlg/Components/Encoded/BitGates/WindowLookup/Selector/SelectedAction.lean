/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.FrameLaws

/-!
# Selected static leaf actions and the clean prefix invariant

The selected action reads the original most-significant-first address. It
protects every address and stack field and ignores temporary prefix flips
whenever all actual leaf payload actions have those same properties.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The one static leaf selected by the original address; missing leaves act as identity. -/
def selectedActionAt (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data) :
    {remaining : Nat} → (tree : SelectorTrie remaining) →
      (depth : Nat) → depth + remaining = width →
      (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width → Data → Data
  | _, .skip _, _, _, _, _, state => state
  | 0, .leaf, _, _, offset, bounded, state =>
      action ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ state
  | remaining + 1, .fork left right, depth, fits, offset, bounded, state =>
      if (frame.addressAt depth (by omega)).get state then
        frame.selectedActionAt action right (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded) state
      else frame.selectedActionAt action left (depth + 1) (by omega)
        offset (left_bound bounded) state

/-- Static branch selection preserves the whole physical address/prefix interface. -/
lemma selectedActionAt_preserves (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data) (preserves : ∀ label, frame.Preserves (action label))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    frame.Preserves (frame.selectedActionAt action tree depth fits offset bounded) := by
  induction tree generalizing depth offset with
  | skip remaining => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | leaf => exact preserves _
  | @fork remaining left right leftIH rightIH =>
      constructor
      · intro index state
        dsimp only [selectedActionAt]
        split
        · exact (rightIH _ (by omega) _ (right_bound bounded)).1 index state
        · exact (leftIH _ (by omega) _ (left_bound bounded)).1 index state
      · intro index state
        dsimp only [selectedActionAt]
        split
        · exact (rightIH _ (by omega) _ (right_bound bounded)).2 index state
        · exact (leftIH _ (by omega) _ (left_bound bounded)).2 index state

/-- Original address guards cannot inspect any temporary selector prefix bit. -/
lemma selectedActionAt_independent (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data)
    (independent : ∀ label, frame.IndependentPrefixes (action label))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    frame.IndependentPrefixes (frame.selectedActionAt action tree depth fits offset bounded) := by
  induction tree generalizing depth offset with
  | skip remaining => exact fun _ _ => rfl
  | leaf => exact independent _
  | @fork remaining left right leftIH rightIH =>
      intro index state
      dsimp only [selectedActionAt]
      rw [EncodedBit.get_flip_of_wire_ne (frame.stack index.succ)
        (frame.addressAt depth (by omega)) (Ne.symm (frame.separate _ _))]
      split
      · exact rightIH _ (by omega) _ (right_bound bounded) index state
      · exact leftIH _ (by omega) _ (left_bound bounded) index state

/-- All future selector prefixes start in their actual zero basis value. -/
def CleanFrom (frame : SelectorFrame encoding width) (depth : Nat) (state : Data) : Prop :=
  ∀ index : Fin width, depth ≤ index.val → (frame.stack index.succ).get state = false

/-- Protecting every stack field preserves the entire unused clean prefix region. -/
lemma cleanFrom_preserved (frame : SelectorFrame encoding width) (action : Data → Data)
    (preserves : frame.Preserves action) (depth : Nat) (state : Data)
    (clean : frame.CleanFrom depth state) : frame.CleanFrom depth (action state) := by
  intro index later
  rw [preserves.2]
  exact clean index later

/-- An explicit conditional payload preserves the same complete protected fields. -/
lemma conditionalAction_preserves (frame : SelectorFrame encoding width)
    (enable : EncodedBit encoding) (action : Data → Data) (preserves : frame.Preserves action) :
    frame.Preserves (conditionalAction enable action) := by
  constructor
  · intro index state
    unfold conditionalAction
    split
    · exact preserves.1 index state
    · rfl
  · intro index state
    unfold conditionalAction
    split
    · exact preserves.2 index state
    · rfl

private lemma prefix_ne_later (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) (index : Fin width) (later : depth + 1 ≤ index.val) :
    (frame.prefixAt depth present).wire ≠ (frame.stack index.succ).wire := by
  intro equal
  have values := congrArg Fin.val (frame.stackDistinct equal)
  change depth + 1 = index.val + 1 at values
  omega

/-- Computing this prefix leaves all deeper initially clean prefix bits untouched. -/
lemma cleanFrom_zeroChild (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) (state : Data) (clean : frame.CleanFrom depth state) :
    frame.CleanFrom (depth + 1)
      (zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) state) := by
  intro index later
  unfold zeroChildStep
  split
  · rw [EncodedBit.get_flip_of_wire_ne _ _ (frame.prefix_ne_later depth present index later)]
    exact clean index (by omega)
  · exact clean index (by omega)

/-- Switching the current child cannot disturb any deeper clean prefix bit. -/
lemma cleanFrom_next (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) (state : Data) (clean : frame.CleanFrom (depth + 1) state) :
    frame.CleanFrom (depth + 1) ((frame.nextGate depth present).step state) := by
  intro index later
  change (frame.stack index.succ).get
    (cnotStep (frame.enableAt depth present) (frame.prefixAt depth present) state) = false
  rw [EncodedBit.cnotStep_get_of_target_ne _ _ _ (frame.prefix_ne_later depth present index later)]
  exact clean index later

/-- Full frame protection and prefix independence supply the exact local fork obligations. -/
lemma forkAction_of_frame (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) (action : Data → Data) (preserves : frame.Preserves action)
    (independent : frame.IndependentPrefixes action) :
    ForkAction (frame.enableAt depth present) (frame.addressAt depth present)
      (frame.prefixAt depth present) action where
  enable_get := preserves.2 _
  address_get := preserves.1 _
  work_get := preserves.2 _
  work_flip := independent ⟨depth, present⟩

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
