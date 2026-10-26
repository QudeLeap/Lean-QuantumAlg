/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Gates

/-!
# Actual native conjunction on the original second comparison helper

The same paid Toffoli is used to compute and restore the conjunction of
the two active quantum controls. Its entire encoded-label action retains
every system other than that original helper [G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The one native gate changes only the original helper, on its two actual control values. -/
lemma activePairGates_step (layout : Layout encoding width) (state : Data) :
    stepList layout.activePairGates state =
      if layout.control.get state && layout.selector.get state then
        (layout.clean 1).flip state else state := rfl

/-- Computing the conjunction preserves every projection insensitive to the original helper. -/
lemma activePairGates_preserves (layout : Layout encoding width) {Value : Type}
    (project : Data → Value)
    (untouched : ∀ state, project ((layout.clean 1).flip state) = project state)
    (state : Data) :
    project (stepList layout.activePairGates state) = project state := by
  rw [activePairGates_step]
  split_ifs <;> first | exact untouched state | rfl

/-- The helper readout keeps its original value xored with the actual coherent conjunction. -/
lemma activePairGates_helper (layout : Layout encoding width) (state : Data) :
    (layout.clean 1).get (stepList layout.activePairGates state) =
      ((layout.clean 1).get state ^^ (layout.control.get state && layout.selector.get state)) :=
  toffoliStep_get_target layout.control layout.selector (layout.clean 1) state

/-- Native conjunction compute and uncompute are the same actual involution on all labels. -/
lemma activePairGates_twice (layout : Layout encoding width) (state : Data) :
    stepList layout.activePairGates (stepList layout.activePairGates state) = state :=
  stepList_reverse_stepList layout.activePairGates state

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
