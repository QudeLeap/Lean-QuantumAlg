/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Rows
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability.Words

/-!
# Every original streaming carry is physically recorded exactly once

The literal increasing-index rows vent precisely records zero through
width-minus-three in that order. The stream performs no stored phase read,
so every original caller Store is admitted before all record cells have
been written [G25, main.tex:199-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Each positive source row contains exactly its matching original physical vent. -/
lemma streamingStep_ventIndices (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    ventIndices (layout.streamingStep wide constant index) =
      if positive : 0 < index.val then [⟨index.val - 1, by omega⟩] else [] := by
  unfold streamingStep
  split_ifs <;> rfl

/-- The actual chronological prefix records each original carry once in increasing order. -/
lemma streamingRows_ventIndices (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    ventIndices (layout.streamingRows wide constant count bounded) =
      List.ofFn (fun record : Fin (count - 1) => (⟨record.val, by omega⟩ : Fin (width - 2))) := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows, ventIndices_append, ih (by omega), streamingStep_ventIndices]
      cases count with
      | zero => rw [dif_neg (by omega : ¬ 0 < 0)]; rfl
      | succ count =>
          rw [dif_pos (Nat.succ_pos count), List.ofFn_succ', List.concat_eq_append]
          rfl

/-- The actual full stream writes all existing record cells exactly once in their original order. -/
lemma streamingWord_ventIndices (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    ventIndices (layout.streamingWord wide constant) =
      List.ofFn (fun record : Fin (width - 2) => record) := by
  rw [streamingWord_eq_rows]
  change ventIndices (layout.streamingRows wide constant (width - 1) le_rfl) = _
  have actual := streamingRows_ventIndices layout wide constant (width - 1) le_rfl
  have countEq : width - 1 - 1 = width - 2 := by omega
  rw [List.ofFn_congr countEq] at actual
  simpa only [Fin.val_cast, Fin.eta] using actual

/-- The same actual source row performs no paid stored-result phase read. -/
lemma streamingStep_phaseFree (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    PhaseFree (layout.streamingStep wide constant index) := by
  unfold streamingStep
  split_ifs <;> trivial

/-- Every literal chronological streaming prefix performs no paid stored-result phase read. -/
lemma streamingRows_phaseFree (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    PhaseFree (layout.streamingRows wide constant count bounded) := by
  revert bounded
  induction count with
  | zero => intro _; trivial
  | succ count ih =>
      intro bounded
      rw [streamingRows, phaseFree_append]
      exact ⟨ih (by omega), streamingStep_phaseFree layout wide constant _⟩

/-- The full actual streaming word is ready on every original Store and original bank contents. -/
lemma streamingWord_phaseFree (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) : PhaseFree (layout.streamingWord wide constant) := by
  rw [streamingWord_eq_rows]
  exact streamingRows_phaseFree layout wide constant (width - 1) le_rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
