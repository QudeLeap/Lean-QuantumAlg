/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Controls
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Readout

/-!
# Exact retained physical projections of the paid comparison-control Toffoli

The original target and every system outside the second helper retain their
readouts. The paid conjunction word also commutes with flipping the excluded
reduction flag. These are full encoded-label equalities, independent of any
initialization of dirty systems or the flag [G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Computing the conjunction retains every physical readout outside its original helper. -/
lemma activePairGates_get (layout : Layout encoding width) (observed : EncodedBit encoding)
    (outside : (layout.clean 1).wire ≠ observed.wire) (state : Data) :
    observed.get (stepList layout.activePairGates state) = observed.get state :=
  activePairGates_preserves layout observed.get
    (get_flip_of_wire_ne (layout.clean 1) observed outside) state

/-- The conjunction compute word retains the complete original physical target word. -/
lemma activePairGates_sourceWord (layout : Layout encoding width) (state : Data) :
    layout.sourceWord (stepList layout.activePairGates state) = layout.sourceWord state := by
  unfold sourceWord
  congr 1
  funext index
  exact activePairGates_get layout (layout.target index)
    (layout.wire_ne (by intro impossible; cases impossible)) state

/-- The actual conjunction word commutes with the original excluded flag's physical flip. -/
lemma activePairGates_flag_flip (layout : Layout encoding width) (state : Data) :
    stepList layout.activePairGates (layout.flag.flip state) =
      layout.flag.flip (stepList layout.activePairGates state) := by
  have controlOutside : layout.flag.wire ≠ layout.control.wire :=
    layout.wire_ne (by intro impossible; cases impossible)
  have selectorOutside : layout.flag.wire ≠ layout.selector.wire :=
    layout.wire_ne (by intro impossible; cases impossible)
  rw [activePairGates_step, get_flip_of_wire_ne layout.flag layout.control controlOutside,
    get_flip_of_wire_ne layout.flag layout.selector selectorOutside, activePairGates_step]
  split_ifs
  · exact EncodedBit.flip_comm (layout.clean 1) layout.flag state
  · rfl

/-- The paid flag CNOT xors its actual helper value into an already applied carry mask. -/
lemma comparisonFlagCnot_mask (layout : Layout encoding width) (carry : Bool) (state : Data) :
    cnotStep (layout.clean 1) layout.flag (if carry then layout.flag.flip state else state) =
      if carry ^^ (layout.clean 1).get state then layout.flag.flip state else state := by
  have helperOutside : layout.flag.wire ≠ (layout.clean 1).wire :=
    layout.wire_ne (by intro impossible; cases impossible)
  cases carry <;> cases helper : (layout.clean 1).get state <;>
    simp [cnotStep, get_flip_of_wire_ne layout.flag (layout.clean 1) helperOutside,
      EncodedBit.flip_flip, helper]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
