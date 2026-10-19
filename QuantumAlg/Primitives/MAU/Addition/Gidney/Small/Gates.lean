/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.Offset

/-!
# Literal small-width modular-offset lists

The list concatenates the same three pivot constructions as the small
offset circuit. It exposes their actual X/CNOT instructions for subsequent
coherent control [G17, paper.tex:319-334].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Small

noncomputable section

open Nat.FixedWidth EncodedBit.GateSpec

/-- Literal X/CNOT list for each supported pivot width. -/
def pivotGates : (width : Nat) → width ≤ 2 → Fin (2 ^ width + 1) →
    List (EncodedBit.GateSpec (BinaryLabelEncoding.finIdentity width))
  | 0, _, pivot => Zero.gates pivot
  | 1, _, pivot => One.gates pivot
  | 2, _, pivot => Two.gates pivot
  | width + 3, impossible, _ => False.elim (by omega)

/-- The literal list has the already specified all-input pivot action. -/
lemma pivotGates_step (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) (input : Fin (2 ^ width)) :
    stepList (pivotGates width small pivot) input = pivotWordOutput pivot input := by
  interval_cases width
  · exact Zero.gidneySmallZero_step pivot input
  · exact One.gidneySmallOne_step pivot input
  · exact Two.gidneySmallTwo_step pivot input

/-- Each small pivot emits at most three native instructions. -/
lemma pivotGates_length (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) : (pivotGates width small pivot).length ≤ 3 := by
  interval_cases width <;> fin_cases pivot <;> dsimp only [pivotGates] <;> decide

/-- The literal pivot uses at most two X gates. -/
lemma pivotGates_x_bound (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) :
    ((pivotGates width small pivot).map xMultiplicity).sum ≤ 2 := by
  interval_cases width <;> fin_cases pivot <;> dsimp only [pivotGates] <;> decide

/-- The literal pivot uses at most one CNOT. -/
lemma pivotGates_cnot_bound (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) :
    ((pivotGates width small pivot).map cnotMultiplicity).sum ≤ 1 := by
  interval_cases width <;> fin_cases pivot <;> dsimp only [pivotGates] <;> decide

/-- Execute the original three pivots in their specified order. -/
def modularOffsetGates (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    List (EncodedBit.GateSpec (BinaryLabelEncoding.finIdentity width)) :=
  pivotGates width small (offsetFirstPivot modulus constant) ++
    pivotGates width small modulus ++
      pivotGates width small (offsetLastPivot modulus constant)

/-- Exact list semantics includes the identity extension on noncanonical words. -/
lemma modularOffsetGates_step (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (input : Fin (2 ^ width)) :
    stepList (modularOffsetGates width small modulus constant) input =
      modularWordOutput modulus constant input := by
  simp only [modularOffsetGates, stepList_append, pivotGates_step]
  exact gidneyModularWord_three_pivots modulus constant input

/-- The three actual lists contain at most nine instructions in total. -/
lemma modularOffsetGates_length (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetGates width small modulus constant).length ≤ 9 := by
  simp only [modularOffsetGates, List.length_append]
  have first := pivotGates_length width small (offsetFirstPivot modulus constant)
  have middle := pivotGates_length width small modulus
  have last := pivotGates_length width small (offsetLastPivot modulus constant)
  omega

/-- The three pivots emit at most six X gates. -/
lemma modularOffsetGates_x_bound (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    ((modularOffsetGates width small modulus constant).map xMultiplicity).sum ≤ 6 := by
  simp only [modularOffsetGates, List.map_append, List.sum_append]
  have first := pivotGates_x_bound width small (offsetFirstPivot modulus constant)
  have middle := pivotGates_x_bound width small modulus
  have last := pivotGates_x_bound width small (offsetLastPivot modulus constant)
  omega

/-- The three pivots emit at most three CNOT gates. -/
lemma modularOffsetGates_cnot_bound (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    ((modularOffsetGates width small modulus constant).map cnotMultiplicity).sum ≤ 3 := by
  simp only [modularOffsetGates, List.map_append, List.sum_append]
  have first := pivotGates_cnot_bound width small (offsetFirstPivot modulus constant)
  have middle := pivotGates_cnot_bound width small modulus
  have last := pivotGates_cnot_bound width small (offsetLastPivot modulus constant)
  omega

end

end QuantumAlg.MAU.Addition.Gidney.Small
