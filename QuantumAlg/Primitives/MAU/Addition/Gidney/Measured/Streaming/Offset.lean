/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.Complement

/-!
# Actual offset and complement words on the original target ports

The literal static CNOT list is the existing controlled constant-xor word in
the same order. Its readout and untouched-wire laws therefore apply directly.
Both target complements are likewise the actual existing native X word
[G25, main.tex:209-239,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The same original target ports as the existing encoded-word interface. -/
def targetPorts (layout : Layout encoding width) : Word encoding width where
  bit := layout.target

private lemma flatten_selected {Index Value : Type} (selected : Index → Bool)
    (value : Index → Value) (indices : List Index) :
    (indices.map fun index => if selected index then [value index] else []).flatten =
      (indices.filter selected).map value := by
  induction indices with
  | nil => rfl
  | cons index rest ih => cases chosen : selected index <;> simp [chosen, ih]

/-- The literal offset list has exactly the original static controlled-xor construction. -/
lemma offsetGates_eq_controlledXor (layout : Layout encoding width)
    (constant : BitVec width) :
    layout.offsetGates constant =
      Word.controlledXorConstantGates layout.control layout.targetPorts constant.toFin
        layout.control_target_ne := by
  unfold offsetGates
  have same :
      (List.ofFn fun index : Fin width =>
        if constant.getLsbD index.val then
          [GateSpec.cnot layout.control (layout.target index) (layout.control_target_ne index)]
        else []) =
      (List.ofFn fun index : Fin width => index).map (fun index =>
        if constant.toNat.testBit index.val then
          [GateSpec.cnot layout.control (layout.target index) (layout.control_target_ne index)]
        else []) := by
    simp only [List.map_ofFn, Function.comp_def, BitVec.testBit_toNat]
  rw [same, flatten_selected]
  rfl

/-- Every original target bit receives exactly its selected static offset xor. -/
lemma offsetGates_target (layout : Layout encoding width) (constant : BitVec width)
    (state : Data) (index : Fin width) :
    (layout.target index).get (stepList (layout.offsetGates constant) state) =
      ((layout.target index).get state ^^
        (constant.getLsbD index.val && layout.control.get state)) := by
  rw [offsetGates_eq_controlledXor]
  have actual := Word.controlledXorConstantStep_get_target layout.control layout.targetPorts
    constant.toFin layout.control_target_ne index
    (fun other different => layout.target_target_ne different) state
  change (layout.target index).get
      (stepList (Word.controlledXorConstantGates layout.control layout.targetPorts constant.toFin
        layout.control_target_ne) state) =
    ((layout.target index).get state ^^
      (layout.control.get state && constant.toNat.testBit index.val)) at actual
  simpa only [BitVec.testBit_toNat, Bool.and_comm] using actual

/-- The actual offset word preserves every observed wire outside the original target word. -/
lemma offsetGates_other (layout : Layout encoding width) (constant : BitVec width)
    (observed : EncodedBit encoding)
    (different : ∀ index, (layout.target index).wire ≠ observed.wire) (state : Data) :
    observed.get (stepList (layout.offsetGates constant) state) = observed.get state := by
  rw [offsetGates_eq_controlledXor]
  exact Word.controlledXorConstantStep_get_observed_of_target_ne layout.control layout.targetPorts
    constant.toFin layout.control_target_ne observed different state

/-- The actual target complement is the same complete native X word in the same order. -/
lemma complementGates_eq_word (layout : Layout encoding width) :
    layout.complementGates = layout.targetPorts.complementGates := by
  simp only [complementGates, Word.complementGates, List.map_ofFn, Function.comp_def, targetPorts]

/-- Every original target bit is complemented exactly once. -/
lemma complementGates_target (layout : Layout encoding width) (state : Data)
    (index : Fin width) :
    (layout.target index).get (stepList layout.complementGates state) =
      !(layout.target index).get state := by
  rw [complementGates_eq_word]
  exact Word.complementGates_get layout.targetPorts
    (by
      intro first second same
      have ports : (.inr (.inl first) : Port width) = .inr (.inl second) :=
        layout.distinct same
      exact Sum.inl.inj (Sum.inr.inj ports)) state index

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
