/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.SubLayouts
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction.Program
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction.Cancellation
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Four actual conjunction calls with one restored dirty bit

The literal list is F, G, F, G. Each subcall restores its temporary control
group, so the proved predicate cancellation applies to the full encoded
state. The final action changes only the output by the conjunction of all
original controls. Neither the external work bit nor the temporary control
bits need to be zero. Length counts the actual elementary gate list.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)

private def allBits {width : Nat} (bits : Fin width → EncodedBit encoding) (state : Data) : Bool :=
  decide (∀ index, (bits index).get state = true)

private theorem allBits_flip {width : Nat} (bits : Fin width → EncodedBit encoding)
    (target : EncodedBit encoding) (different : ∀ index, target.wire ≠ (bits index).wire)
    (state : Data) : allBits bits (target.flip state) = allBits bits state := by
  have values (index : Fin width) := get_flip_of_wire_ne target (bits index) (different index) state
  simp only [allBits, values]

/-- The predicate reads the original larger control group. -/
def firstPredicate (state : Data) : Bool := allBits layout.firstBit state

/-- The predicate reads the original smaller control group. -/
def secondPredicate (state : Data) : Bool := allBits layout.secondBit state

/-- The first actual subcall flips the external dirty bit and restores all temporary wires. -/
def firstGates (large : 3 ≤ controls) : List (GateSpec encoding) :=
  (layout.firstSubLayout large).borrowedAndGates

/-- The second actual subcall flips the output and restores all temporary wires. -/
def secondGates (large : 3 ≤ controls) : List (GateSpec encoding) :=
  (layout.secondSubLayout large).borrowedAndGates

/-- Four literal elementary subcalls cancel the arbitrary incoming work value. -/
def balancedGates (large : 3 ≤ controls) : List (GateSpec encoding) :=
  layout.firstGates large ++ layout.secondGates large ++
    layout.firstGates large ++ layout.secondGates large

private theorem firstSubLayout_conjunction (large : 3 ≤ controls) (state : Data) :
    (layout.firstSubLayout large).sourceConjunction state (firstWidth controls - 2 + 2) =
      layout.firstPredicate state := by
  apply Bool.eq_iff_iff.mpr
  rw [ZeroTestLayout.sourceConjunction_eq_true_iff, firstSubLayout_source_all]
  simp only [firstPredicate, allBits, decide_eq_true_eq]

private theorem secondSubLayout_conjunction (large : 3 ≤ controls) (state : Data) :
    (layout.secondSubLayout large).sourceConjunction state (secondWidth controls - 1 + 2) =
      (layout.secondPredicate state && layout.work.get state) := by
  apply Bool.eq_iff_iff.mpr
  rw [ZeroTestLayout.sourceConjunction_eq_true_iff, secondSubLayout_source_all,
    Bool.and_eq_true_iff]
  simp only [secondPredicate, allBits, decide_eq_true_eq]

theorem firstGates_step (large : 3 ≤ controls) (state : Data) :
    GateSpec.stepList (layout.firstGates large) state =
      predicateFlip layout.work layout.firstPredicate state := by
  have output : (layout.firstSubLayout large).output = layout.work := rfl
  unfold firstGates predicateFlip
  rw [ZeroTestLayout.borrowedAndGates_step, firstSubLayout_conjunction, output]

theorem secondGates_step (large : 3 ≤ controls) (state : Data) :
    GateSpec.stepList (layout.secondGates large) state =
      predicateFlip layout.output
        (fun value => layout.secondPredicate value && layout.work.get value) state := by
  have output : (layout.secondSubLayout large).output = layout.output := rfl
  unfold secondGates predicateFlip
  rw [ZeroTestLayout.borrowedAndGates_step, secondSubLayout_conjunction, output]

private theorem firstPredicate_work_flip (state : Data) :
    layout.firstPredicate (layout.work.flip state) = layout.firstPredicate state :=
  allBits_flip layout.firstBit layout.work
    (fun index => (layout.source_work_ne (firstIndex index)).symm) state

private theorem firstPredicate_output_flip (state : Data) :
    layout.firstPredicate (layout.output.flip state) = layout.firstPredicate state :=
  allBits_flip layout.firstBit layout.output
    (fun index => (layout.source_output_ne (firstIndex index)).symm) state

private theorem secondPredicate_work_flip (state : Data) :
    layout.secondPredicate (layout.work.flip state) = layout.secondPredicate state :=
  allBits_flip layout.secondBit layout.work
    (fun index => (layout.source_work_ne (secondIndex index)).symm) state

private theorem secondPredicate_output_flip (state : Data) :
    layout.secondPredicate (layout.output.flip state) = layout.secondPredicate state :=
  allBits_flip layout.secondBit layout.output
    (fun index => (layout.source_output_ne (secondIndex index)).symm) state

private theorem predicates_and (state : Data) :
    (layout.firstPredicate state && layout.secondPredicate state) =
      decide (∀ index, (layout.source.bit index).get state = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true_iff, firstPredicate, secondPredicate, allBits, decide_eq_true_eq]
  exact (layout.source_all_iff state).symm

/-- The full encoded state is restored except for the output xor of all original controls. -/
theorem balancedGates_step (large : 3 ≤ controls) (state : Data) :
    GateSpec.stepList (layout.balancedGates large) state =
      if ∀ index, (layout.source.bit index).get state = true
        then layout.output.flip state else state := by
  calc
    _ = dirtyPredicateConjunction layout.work layout.output
        layout.firstPredicate layout.secondPredicate state := by
      simp only [balancedGates, GateSpec.stepList_append, firstGates_step, secondGates_step,
        dirtyPredicateConjunction]
    _ = predicateFlip layout.output
        (fun value => layout.firstPredicate value && layout.secondPredicate value) state :=
      dirtyPredicateConjunction_eq layout.work layout.output layout.work_output_ne
        layout.firstPredicate layout.secondPredicate
        (layout.firstPredicate_work_flip) (layout.firstPredicate_output_flip)
        (layout.secondPredicate_work_flip) (layout.secondPredicate_output_flip) state
    _ = _ := by
      rw [predicateFlip, predicates_and]
      simp only [decide_eq_true_eq]

/-- The literal elementary program has the complete all-input encoded conjunction action. -/
theorem balancedGates_realizes (large : 3 ≤ controls) :
    UnitaryCircuit.Realizes encoding (GateSpec.programList (layout.balancedGates large))
      (fun state => if ∀ index, (layout.source.bit index).get state = true
        then layout.output.flip state else state) :=
  GateSpec.realizesList_congrStep (layout.balancedGates large) (layout.balancedGates_step large)

private theorem subcall_length {tail : Nat}
    (sublayout : ZeroTestLayout (encoding := encoding) tail) :
    sublayout.borrowedAndGates.length = if tail = 0 then 1 else 4 * tail := by
  by_cases empty : tail = 0
  · simp only [ZeroTestLayout.borrowedAndGates, if_pos empty, List.length_singleton]
  · simp only [ZeroTestLayout.borrowedAndGates, if_neg empty]
    exact ZeroTestLayout.dirtyConjunctionGates_length _ (Nat.pos_of_ne_zero empty)

/-- Exact elementary length counts both occurrences of each actual borrowed-work subcall. -/
theorem balancedGates_length (large : 3 ≤ controls) :
    (layout.balancedGates large).length =
      2 * ((if firstWidth controls - 2 = 0 then 1 else 4 * (firstWidth controls - 2)) +
        (if secondWidth controls - 1 = 0 then 1 else 4 * (secondWidth controls - 1))) := by
  simp only [balancedGates, List.length_append, firstGates, secondGates, subcall_length]
  omega

/-- The actual elementary list has linear length using just the one external dirty bit. -/
theorem balancedGates_length_le (large : 3 ≤ controls) :
    (layout.balancedGates large).length ≤ 8 * controls := by
  rw [balancedGates_length]
  have balanced := balanced_widths large
  have partition := width_partition controls
  split <;> split <;> omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
