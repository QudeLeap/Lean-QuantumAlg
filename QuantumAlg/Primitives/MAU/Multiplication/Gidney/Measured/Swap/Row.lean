/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Actual original readouts and complete untouched projections of one Fredkin row

The native one-Toffoli row exchanges only its paired source/target bits,
selected by the original coherent global control. All other projections
preserved by those two physical flips retain their exact original values
[VBE95, 9511018.tex:333-367; G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete original label after exchanging exactly one paired original word bit. -/
def swapRowLabel (layout : Layout encoding width) (selected : Fin width) : Data → Data :=
  swapStep (layout.source selected) (layout.target selected)
    (layout.wire_ne (by intro impossible; cases impossible))

/-- The same actual native row has the complete original conditional exchange action. -/
lemma swapRowGates_step (layout : Layout encoding width) (selected : Fin width) (state : Data) :
    stepList (layout.swapRowGates selected) state =
      if layout.control.get state then layout.swapRowLabel selected state else state := by
  exact fredkin_step_eq_if layout.control (layout.source selected) (layout.target selected)
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible)) state

/-- The exchanged original source readout changes exactly at its paired bit. -/
lemma swapRowLabel_source (layout : Layout encoding width) (selected observed : Fin width)
    (state : Data) :
    (layout.source observed).get (layout.swapRowLabel selected state) =
      if observed = selected then (layout.target observed).get state else
        (layout.source observed).get state := by
  by_cases same : observed = selected
  · subst observed
    rw [if_pos rfl]
    exact swapStep_get_left _ _ _ state
  · rw [if_neg same]
    exact swapStep_get_observed_of_swap_ne _ _ _ _
      (layout.wire_ne (by
        intro equal
        exact same (Sum.inl.inj (Sum.inr.inj equal)).symm))
      (layout.wire_ne (by intro impossible; cases impossible)) state

/-- The exchanged original target readout changes exactly at its paired bit. -/
lemma swapRowLabel_target (layout : Layout encoding width) (selected observed : Fin width)
    (state : Data) :
    (layout.target observed).get (layout.swapRowLabel selected state) =
      if observed = selected then (layout.source observed).get state else
        (layout.target observed).get state := by
  by_cases same : observed = selected
  · subst observed
    rw [if_pos rfl]
    exact swapStep_get_right _ _ _ state
  · rw [if_neg same]
    exact swapStep_get_observed_of_swap_ne _ _ _ _
      (layout.wire_ne (by intro impossible; cases impossible))
      (layout.wire_ne (by
        intro equal
        exact same (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj equal))).symm)) state

/-- The actual native row retains every projection invariant under its two possible target flips. -/
lemma swapRowGates_preserves_projection (layout : Layout encoding width) (selected : Fin width)
    {Projection : Type} (project : Data → Projection)
    (source : ∀ state, project ((layout.source selected).flip state) = project state)
    (target : ∀ state, project ((layout.target selected).flip state) = project state)
    (state : Data) : project (stepList (layout.swapRowGates selected) state) = project state := by
  apply stepList_preserves_of_targetFlipPreserves
  intro gate member
  simp only [swapRowGates, fredkinGates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact target
  · exact source
  · exact target

/-- The same original coherent global control is retained by the actual native exchange. -/
lemma swapRowGates_control (layout : Layout encoding width) (selected : Fin width)
    (state : Data) :
    layout.control.get (stepList (layout.swapRowGates selected) state) =
      layout.control.get state :=
  swapRowGates_preserves_projection layout selected layout.control.get
    (get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    (get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible))) state

/-- Every original source bit has exactly its selected exchanged or retained actual readout. -/
lemma swapRowGates_source (layout : Layout encoding width) (selected observed : Fin width)
    (state : Data) :
    (layout.source observed).get (stepList (layout.swapRowGates selected) state) =
      if observed = selected then
        (if layout.control.get state then (layout.target observed).get state else
          (layout.source observed).get state) else (layout.source observed).get state := by
  rw [swapRowGates_step]
  by_cases enabled : layout.control.get state = true
  · simp only [if_pos enabled]
    exact swapRowLabel_source layout selected observed state
  · simp only [if_neg enabled, ite_self]

/-- Every original target bit has exactly its selected exchanged or retained actual readout. -/
lemma swapRowGates_target (layout : Layout encoding width) (selected observed : Fin width)
    (state : Data) :
    (layout.target observed).get (stepList (layout.swapRowGates selected) state) =
      if observed = selected then
        (if layout.control.get state then (layout.source observed).get state else
          (layout.target observed).get state) else (layout.target observed).get state := by
  rw [swapRowGates_step]
  by_cases enabled : layout.control.get state = true
  · simp only [if_pos enabled]
    exact swapRowLabel_target layout selected observed state
  · simp only [if_neg enabled, ite_self]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
