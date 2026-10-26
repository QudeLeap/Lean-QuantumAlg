/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Rows
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Coordinates

/-!
# Actual CNOT and paid one-qubit coordinates of chronological streaming

The low row has no incoming carry extraction or affine conjugations. Each
other row retains its two extraction CNOTs, two possible affine CNOTs and
one possible offset CNOT. Every actual vent pays H and its possible reset X
[G25, main.tex:199-251,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma offsetGates_coordinates (layout : Layout encoding width)
    (constant : BitVec width) :
    ((layout.offsetGates constant).map cnotMultiplicity).sum ≤ width ∧
      ((layout.offsetGates constant).map xMultiplicity).sum = 0 := by
  simp only [offsetGates, List.map_flatten, List.map_ofFn, Function.comp_def,
    List.sum_flatten, List.sum_ofFn]
  constructor
  · calc
      _ ≤ ∑ _ : Fin width, 1 := by
        apply Finset.sum_le_sum
        intro index _
        split <;> simp [cnotMultiplicity]
      _ = width := by simp
  · apply Finset.sum_eq_zero
    intro index _
    split <;> simp [xMultiplicity]

private lemma computeCarryGates_coordinates (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    ((layout.computeCarryGates wide constant index).map cnotMultiplicity).sum ≤
        (if index.val = 0 then 0 else 2) ∧
      ((layout.computeCarryGates wide constant index).map xMultiplicity).sum = 0 := by
  unfold computeCarryGates
  dsimp only
  split
  · split <;> simp_all [cnotMultiplicity, xMultiplicity]
  · cases constant.getLsbD index.val <;>
      simp_all [affineToffoliGates, cnotMultiplicity, xMultiplicity]

private lemma extractCarryGates_coordinates (layout : Layout encoding width)
    (index : Fin (width - 1)) :
    ((layout.extractCarryGates index).map cnotMultiplicity).sum =
        (if 0 < index.val then 2 else 0) ∧
      ((layout.extractCarryGates index).map xMultiplicity).sum = 0 := by
  unfold extractCarryGates
  split <;> simp_all [cnotMultiplicity, xMultiplicity]

private lemma finishCarryGates_coordinates (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    ((layout.finishCarryGates wide constant index).map cnotMultiplicity).sum ≤ 1 ∧
      ((layout.finishCarryGates wide constant index).map xMultiplicity).sum = 0 := by
  unfold finishCarryGates
  split <;> simp [cnotMultiplicity, xMultiplicity]

/-- The source low row has at most one CNOT; every later source row has at most five. -/
lemma streamingStep_cnot_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    wordCnotCount (layout.streamingStep wide constant index) ≤
      if index.val = 0 then 1 else 5 := by
  have compute := (computeCarryGates_coordinates layout wide constant index).1
  have extract := (extractCarryGates_coordinates layout index).1
  have finish := (finishCarryGates_coordinates layout wide constant index).1
  rw [streamingStep, wordCnotCount_append, wordCnotCount_append]
  have ventZero : wordCnotCount (encoding := encoding) (records := width - 2)
      (if positive : 0 < index.val then
        [.vent (layout.carryHelper index.val) ⟨index.val - 1, by omega⟩] else []) = 0 := by
    split <;> rfl
  rw [ventZero]
  change ((layout.computeCarryGates wide constant index).map cnotMultiplicity).sum +
    ((layout.extractCarryGates index).map cnotMultiplicity).sum + 0 +
      ((layout.finishCarryGates wide constant index).map cnotMultiplicity).sum ≤ _
  by_cases positive : 0 < index.val
  · have different : index.val ≠ 0 := by omega
    rw [if_neg different] at compute ⊢
    rw [if_pos positive] at extract
    omega
  · have first : index.val = 0 := by omega
    rw [if_pos first] at compute ⊢
    rw [if_neg positive] at extract
    omega

/-- Every non-low streaming row includes its actual H and possible reset X. -/
lemma streamingStep_single_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    wordSingleQubitBound (layout.streamingStep wide constant index) =
      if 0 < index.val then 2 else 0 := by
  have compute := (computeCarryGates_coordinates layout wide constant index).2
  have extract := (extractCarryGates_coordinates layout index).2
  have finish := (finishCarryGates_coordinates layout wide constant index).2
  rw [streamingStep, wordSingleQubitBound_append, wordSingleQubitBound_append]
  have ventBound : wordSingleQubitBound (encoding := encoding) (records := width - 2)
      (if positive : 0 < index.val then
        [.vent (layout.carryHelper index.val) ⟨index.val - 1, by omega⟩] else []) =
        if 0 < index.val then 2 else 0 := by
    split <;> rfl
  rw [ventBound]
  change ((layout.computeCarryGates wide constant index).map xMultiplicity).sum +
    ((layout.extractCarryGates index).map xMultiplicity).sum + _ +
      ((layout.finishCarryGates wide constant index).map xMultiplicity).sum = _
  rw [compute, extract, finish]
  omega

private lemma streamingRows_cnot_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    wordCnotCount (layout.streamingRows wide constant count bounded) ≤ 5 * count - 4 := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows, wordCnotCount_append]
      have row := streamingStep_cnot_bound layout wide constant ⟨count, by omega⟩
      change wordCnotCount (layout.streamingStep wide constant ⟨count, by omega⟩) ≤
        if count = 0 then 1 else 5 at row
      have earlier := ih (by omega)
      cases count with
      | zero =>
          rw [if_pos rfl] at row
          simpa only [streamingRows, wordCnotCount, List.map_nil, List.sum_nil,
            Nat.zero_add] using row
      | succ count =>
          rw [if_neg (by omega : count + 1 ≠ 0)] at row
          omega

private lemma streamingRows_single_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    wordSingleQubitBound (layout.streamingRows wide constant count bounded) = 2 * (count - 1) := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows, wordSingleQubitBound_append, ih (by omega), streamingStep_single_bound]
      change 2 * (count - 1) + (if 0 < count then 2 else 0) = 2 * (count + 1 - 1)
      split <;> omega

/-- The complete actual streaming word includes at most six CNOTs per bit, with its low saving. -/
lemma streamingWord_cnot_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordCnotCount (layout.streamingWord wide constant) ≤ 6 * width - 9 := by
  rw [streamingWord_eq_rows]
  change ((layout.offsetGates constant).map cnotMultiplicity).sum +
    wordCnotCount (layout.streamingRows wide constant (width - 1) le_rfl) ≤ _
  have offset := (offsetGates_coordinates layout constant).1
  have rows := streamingRows_cnot_bound layout wide constant (width - 1) le_rfl
  omega

/-- Actual streaming has exactly the uniform bound charging both H and possible reset X per vent. -/
lemma streamingWord_single_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordSingleQubitBound (layout.streamingWord wide constant) = 2 * (width - 2) := by
  rw [streamingWord_eq_rows]
  change ((layout.offsetGates constant).map xMultiplicity).sum +
    wordSingleQubitBound (layout.streamingRows wide constant (width - 1) le_rfl) = _
  rw [(offsetGates_coordinates layout constant).2, Nat.zero_add, streamingRows_single_bound]
  congr 1

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
