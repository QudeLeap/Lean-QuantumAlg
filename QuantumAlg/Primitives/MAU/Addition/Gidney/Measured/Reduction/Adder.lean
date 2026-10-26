/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Readout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Isometry

/-!
# Actual measured-adder readouts at the original modular-reduction ports

The measured adder uses the original flag as its quantum control. Its same
physical target, dirty word and two helpers retain the proved behavior;
both original active controls lie outside its complete port set
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual reused adder returns both original helpers physically to zero. -/
lemma reductionAdder_clean (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) (helper : Fin 2) :
    (layout.clean helper).get
      (wordLabel (layout.adderLayout.adderWord wide constant) state) = false :=
  Measured.Layout.adderWord_clean_get layout.adderLayout wide constant state clean helper

/-- The same original flag is retained as the coherent control of the actual measured adder. -/
lemma reductionAdder_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) :
    layout.flag.get (wordLabel (layout.adderLayout.adderWord wide constant) state) =
      layout.flag.get state :=
  Measured.Layout.adderWord_control_get layout.adderLayout wide constant state clean

/-- Every original arbitrary dirty port is restored by the actual adder at the reused placement. -/
lemma reductionAdder_dirty (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) (index : Fin (width - 2)) :
    (layout.dirty index).get
        (wordLabel (layout.adderLayout.adderWord wide constant) state) =
      (layout.dirty index).get state :=
  Measured.Layout.adderWord_dirty_get layout.adderLayout wide constant state clean index

/-- The complete actual target readout is finite addition controlled by that same original flag. -/
lemma reductionAdder_sourceWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) :
    layout.sourceWord (wordLabel (layout.adderLayout.adderWord wide constant) state) =
      layout.sourceWord state + if layout.flag.get state then constant else 0 :=
  Measured.Layout.adderWord_targetWord layout.adderLayout wide constant state clean

/-- Every physically excluded original readout is retained by the complete measured adder. -/
lemma reductionAdder_outside (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (observed : EncodedBit encoding)
    (outside : ∀ port, (layout.adderLayout.bit port).wire ≠ observed.wire) (state : Data) :
    observed.get (wordLabel (layout.adderLayout.adderWord wide constant) state) =
      observed.get state := by
  rw [← observed.get_eq, ← observed.get_eq]
  exact Measured.Layout.adderWord_wire_read layout.adderLayout wide constant observed.wire
    outside state

/-- Both active quantum controls are excluded from every reused measured-adder physical port. -/
lemma reductionAdder_active_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin 2) (state : Data) :
    (layout.bit (.inl index)).get
        (wordLabel (layout.adderLayout.adderWord wide constant) state) =
      (layout.bit (.inl index)).get state := by
  apply reductionAdder_outside
  intro port
  rcases port with singleton | target | dirty | helper
  · cases singleton
    exact layout.wire_ne (by intro impossible; cases impossible)
  · exact layout.wire_ne (by intro impossible; cases impossible)
  · exact layout.wire_ne (by intro impossible; cases impossible)
  · exact layout.wire_ne (by intro impossible; cases impossible)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
