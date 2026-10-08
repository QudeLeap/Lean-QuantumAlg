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

open Nat.FixedWidth EncodedBit GateSpec

/-- The word is pivot-reflected while both arbitrary bits retain their initial values. -/
def pivotOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : Registers width :=
  (state.1, (pivotWordOutput pivot state.2.1, state.2.2))

/-- The four literal native blocks, in the original execution order. -/
def pivotGates (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    List (GateSpec (encoding width)) :=
  ((biFlipGates width pivot ++ comparisonGates width pivot) ++
    biFlipGates width pivot) ++ comparisonGates width pivot

/-- The four blocks restore both arbitrary bits and implement the pivot reflection. -/
theorem gidneyPivotGates_step (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : Registers width) :
    stepList (pivotGates width pivot) state = pivotOutput pivot state := by
  simp only [pivotGates, stepList_append, gidneyBiFlipGates_step, gidneyComparisonGates_step]
  rcases state with ⟨flag, input, helper⟩
  exact congrArg (fun output : Bool × Fin (2 ^ width) =>
    (output.1, (output.2, helper))) (gidneyBiFlip_four_steps pivot (flag, input))

/-- Emit the actual expanded four-block construction on the fixed carrier. -/
def pivotProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (pivotGates width pivot)

/-- Exact amplitudes and restored arbitrary bits for the actual native program. -/
theorem gidneyPivot_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (pivotProgram width pivot) (pivotOutput pivot) :=
  realizesList_congrStep _ _ _ (gidneyPivotGates_step width pivot)

/-- The pivot retains the original word and two-bit interface. -/
theorem gidneyPivot_interface (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (width + 2) :=
  gidneyBiFlip_interface width pivot

/-- The circuit's native ledger consists of the four actual component ledgers. -/
theorem gidneyPivot_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width pivot).eventCost =
      (biFlipProgram width pivot).eventCost + (comparisonProgram width pivot).eventCost +
        (biFlipProgram width pivot).eventCost + (comparisonProgram width pivot).eventCost := by
  rw [pivotProgram, programList_eventCost, pivotGates]
  simp only [List.map_append, ResourcePool.ofList_append,
    gidneyComparisonGates_eventCost, ← gidneyBiFlip_eventCost]

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
      (layout := QubitLayout.canonical ((encoding width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width (pivotProgram width pivot))
      (fun state => (pivotOutput pivot state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference) (gidneyPivot_realizes width pivot)

end

end QuantumAlg.MAU.Addition.Gidney
