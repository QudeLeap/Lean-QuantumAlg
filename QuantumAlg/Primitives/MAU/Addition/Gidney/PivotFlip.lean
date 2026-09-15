/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.BiFlip

/-!
# Actual four-block pivot reflection

The executed sequence is controlled bi-flip, xor comparison, controlled
bi-flip, xor comparison. Predicate invariance and the bi-flip involution
cancel the arbitrary initial flag [G17, paper.tex:276-293]. The HRS helper
is restored within every block. All target labels, widths, and fitted
pivots are included, with exact amplitudes and no phase allowance.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth

/-- The word is pivot-reflected while both arbitrary bits retain their initial values. -/
def pivotOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : Registers width :=
  (state.1, (pivotWordOutput pivot state.2.1, state.2.2))

/-- The literal four real component programs in execution order. -/
def pivotProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (((biFlipProgram width pivot).seq (comparisonProgram width pivot)).seq
    (biFlipProgram width pivot)).seq (comparisonProgram width pivot)

/-- The actual four-block program restores both arbitrary bits and implements the pivot flip. -/
theorem gidneyPivot_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (pivotProgram width pivot) (pivotOutput pivot) := by
  have hb := gidneyBiFlip_realizes width pivot
  have hc := gidneyComparison_realizes width pivot
  apply (((hb.seq hc).seq hb).seq hc).congrStep
  rintro ⟨flag, input, helper⟩
  exact congrArg (fun output : Bool × Fin (2 ^ width) =>
    (output.1, (output.2, helper))) (gidneyBiFlip_four_steps pivot (flag, input))

/-- The final complete comparison footprint fixes the same canonical full physical list. -/
theorem gidneyPivot_physical (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).physical_idx = List.range (width + 2) := by
  have hb := gidneyBiFlip_physical_range width pivot
  have hc : (comparisonProgram width pivot).physical_idx ⊆ List.range (width + 2) := by
    rw [gidneyComparison_physical]
    exact fun _ h => h
  have hprefix := UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ hb hc) hb
  change ((biFlipProgram width pivot).seq (comparisonProgram width pivot)).physical_idx ∪
      (biFlipProgram width pivot).physical_idx ∪ (comparisonProgram width pivot).physical_idx =
    List.range (width + 2)
  rw [gidneyComparison_physical]
  exact hprefix.union_eq_right

/-- The circuit's native ledger consists of the four actual component ledgers. -/
theorem gidneyPivot_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).eventCost =
      (biFlipProgram width pivot).eventCost + (comparisonProgram width pivot).eventCost +
        (biFlipProgram width pivot).eventCost + (comparisonProgram width pivot).eventCost := by
  simp only [pivotProgram, UnitaryCircuit.seq_eventCost]

/-- The arbitrary flag is returned independently of its value and of the target word. -/
theorem gidneyPivot_flag {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : (pivotOutput pivot state).1 = state.1 := rfl

/-- The HRS helper is returned independently of its value and of the target word. -/
theorem gidneyPivot_helper {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : (pivotOutput pivot state).2.2 = state.2.2 := rfl

/-- Exact joint-basis equality extends to an arbitrary encoded external reference. -/
theorem gidneyPivot_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (UnitaryCircuit.prodLeft (n := reference.width) (pivotProgram width pivot))
      (fun state => (pivotOutput pivot state.1, state.2)) :=
  (gidneyPivot_realizes width pivot).prodLeft

end

end QuantumAlg.MAU.Addition.Gidney
