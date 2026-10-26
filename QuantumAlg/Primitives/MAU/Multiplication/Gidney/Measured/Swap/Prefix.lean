/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Row
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Exact original readouts of every actual controlled-word exchange prefix

The original control remains retained between all native rows. Each source
and target bit is exchanged once at its actual source-order position and
retained by every other row, on arbitrary original labels
[VBE95, 9511018.tex:333-367; G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every native prefix retains each projection unchanged by all original word-bit flips. -/
lemma swapPrefixGates_preserves_projection (layout : Layout encoding width)
    (count : Nat) (bounded : count ≤ width) {Projection : Type} (project : Data → Projection)
    (source : ∀ index state, project ((layout.source index).flip state) = project state)
    (target : ∀ index state, project ((layout.target index).flip state) = project state)
    (state : Data) : project (stepList (layout.swapPrefixGates count bounded) state) =
      project state := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [swapPrefixGates, stepList_append,
        swapRowGates_preserves_projection layout _ project (source _) (target _)]
      exact ih (by omega)

/-- The actual complete original global control is retained through every native prefix. -/
lemma swapPrefixGates_control (layout : Layout encoding width) (count : Nat)
    (bounded : count ≤ width) (state : Data) :
    layout.control.get (stepList (layout.swapPrefixGates count bounded) state) =
      layout.control.get state :=
  swapPrefixGates_preserves_projection layout count bounded layout.control.get
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    (fun _ => get_flip_of_wire_ne _ _ (layout.wire_ne (by intro impossible; cases impossible)))
    state

/-- Every actual prefix has exactly its independent selected source/target readout specification. -/
lemma swapPrefixGates_readouts (layout : Layout encoding width) (count : Nat)
    (bounded : count ≤ width) (state : Data) (observed : Fin width) :
    ((layout.source observed).get (stepList (layout.swapPrefixGates count bounded) state) =
      if observed.val < count then
        (if layout.control.get state then (layout.target observed).get state else
          (layout.source observed).get state) else (layout.source observed).get state) ∧
    ((layout.target observed).get (stepList (layout.swapPrefixGates count bounded) state) =
      if observed.val < count then
        (if layout.control.get state then (layout.source observed).get state else
          (layout.target observed).get state) else (layout.target observed).get state) := by
  induction count with
  | zero => simp [swapPrefixGates, stepList]
  | succ count ih =>
      rw [swapPrefixGates, stepList_append]
      have earlier := ih (by omega)
      constructor
      · rw [swapRowGates_source, swapPrefixGates_control, earlier.1, earlier.2]
        by_cases same : observed = ⟨count, by omega⟩
        · have sameValue : observed.val = count := congrArg Fin.val same
          have before : ¬ observed.val < count := by omega
          have after : observed.val < count + 1 := by omega
          simp only [if_pos same, if_neg before, if_pos after]
        · by_cases before : observed.val < count
          · have after : observed.val < count + 1 := by omega
            simp only [if_neg same, if_pos before, if_pos after]
          · have after : ¬ observed.val < count + 1 := by
              have different : observed.val ≠ count := fun equal => same (Fin.ext equal)
              omega
            simp only [if_neg same, if_neg before, if_neg after]
      · rw [swapRowGates_target, swapPrefixGates_control, earlier.1, earlier.2]
        by_cases same : observed = ⟨count, by omega⟩
        · have sameValue : observed.val = count := congrArg Fin.val same
          have before : ¬ observed.val < count := by omega
          have after : observed.val < count + 1 := by omega
          simp only [if_pos same, if_neg before, if_pos after]
        · by_cases before : observed.val < count
          · have after : observed.val < count + 1 := by omega
            simp only [if_neg same, if_pos before, if_pos after]
          · have after : ¬ observed.val < count + 1 := by
              have different : observed.val ≠ count := fun equal => same (Fin.ext equal)
              omega
            simp only [if_neg same, if_neg before, if_neg after]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
