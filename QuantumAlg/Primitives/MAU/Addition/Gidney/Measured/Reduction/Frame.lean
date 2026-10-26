/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Adder
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Retention
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program

/-!
# Original-system restoration invariant for the actual modular-reduction stages

Every actual stage returns both helpers to zero, retains both original
active controls, restores arbitrary dirty outputs and retains every encoded
wire outside the physical reduction frame. The original reduction flag is
tracked separately by arithmetic [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Complete original-system restoration outside the current target and reduction flag. -/
structure FrameInvariant (layout : Layout encoding width) (initial current : Data) : Prop where
  clean : ∀ helper, (layout.clean helper).get current = false
  active : ∀ index, (layout.bit (.inl index)).get current =
    (layout.bit (.inl index)).get initial
  dirty : ∀ index, (layout.dirty index).get current = (layout.dirty index).get initial
  outside : ∀ observed : Fin encoding.width,
    (∀ port, (layout.bit port).wire ≠ observed) →
    (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val =
      (encoding.encode initial).val.testBit (WireAddress.bitIndex observed).val

/-- The original clean-helper input initializes the frame without restricting any other system. -/
lemma frameInvariant_initial (layout : Layout encoding width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial initial where
  clean := clean
  active := fun _ => rfl
  dirty := fun _ => rfl
  outside := fun _ _ => rfl

/-- A physical xor of only the original flag preserves every frame-restoration invariant. -/
lemma frameInvariant_flag_flip {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) :
    layout.FrameInvariant initial (layout.flag.flip current) where
  clean := fun helper =>
    (get_flip_of_wire_ne layout.flag (layout.clean helper)
      (layout.wire_ne (by intro impossible; cases impossible)) current).trans
        (invariant.clean helper)
  active := fun index =>
    (get_flip_of_wire_ne layout.flag (layout.bit (.inl index))
      (layout.wire_ne (by intro impossible; cases impossible)) current).trans
        (invariant.active index)
  dirty := fun index =>
    (get_flip_of_wire_ne layout.flag (layout.dirty index)
      (layout.wire_ne (by intro impossible; cases impossible)) current).trans
        (invariant.dirty index)
  outside := by
    intro observed outside
    have flagOutside : layout.flag.wire ≠ observed :=
      outside (.inr (.inr (.inr (.inr ()))))
    rw [layout.flag.encode_flip, WireAddress.bit_flipBit_of_ne flagOutside]
    exact invariant.outside observed outside

/-- Selecting that same physical flag xor preserves the frame on either actual control label. -/
lemma frameInvariant_flag_mask {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) (mask : Bool) :
    layout.FrameInvariant initial (if mask then layout.flag.flip current else current) := by
  cases mask
  · exact invariant
  · exact frameInvariant_flag_flip invariant

/-- The entire paid native comparator restores the frame at its actual intermediate input. -/
lemma frameInvariant_comparison {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) (wide : 2 ≤ width)
    (threshold : BitVec width) :
    layout.FrameInvariant initial (stepList (layout.comparisonGates wide threshold) current) := by
  rw [comparisonGates_step layout wide threshold current invariant.clean]
  exact frameInvariant_flag_mask invariant _

/-- The actual paid middle Toffoli changes exactly the original reduction flag. -/
lemma toggleFlagGates_step (layout : Layout encoding width) (current : Data) :
    stepList layout.toggleFlagGates current =
      if layout.control.get current && layout.selector.get current then
        layout.flag.flip current else current := rfl

/-- The paid middle flag toggle restores the same complete original frame. -/
lemma frameInvariant_toggle {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) :
    layout.FrameInvariant initial (stepList layout.toggleFlagGates current) := by
  rw [toggleFlagGates_step]
  exact frameInvariant_flag_mask invariant _

/-- Each actual reused measured addition restores the original controls, dirty and outside wires. -/
lemma frameInvariant_adder {layout : Layout encoding width} {initial current : Data}
    (invariant : layout.FrameInvariant initial current) (wide : 2 ≤ width)
    (constant : BitVec width) :
    layout.FrameInvariant initial
      (wordLabel (layout.adderLayout.adderWord wide constant) current) where
  clean := reductionAdder_clean layout wide constant current invariant.clean
  active := fun index => (reductionAdder_active_get layout wide constant index current).trans
    (invariant.active index)
  dirty := fun index =>
    (reductionAdder_dirty layout wide constant current invariant.clean index).trans
      (invariant.dirty index)
  outside := by
    intro observed outside
    have adderOutside : ∀ port, (layout.adderLayout.bit port).wire ≠ observed := by
      intro port
      rcases port with singleton | target | dirty | helper
      · cases singleton
        exact outside _
      · exact outside _
      · exact outside _
      · exact outside _
    exact (Measured.Layout.adderWord_wire_read layout.adderLayout wide constant observed
      adderOutside current).trans (invariant.outside observed outside)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
