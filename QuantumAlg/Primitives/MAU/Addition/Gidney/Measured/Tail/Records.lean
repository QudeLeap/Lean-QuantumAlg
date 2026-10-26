/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Circuit
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Records

/-!
# Exact physical record order and paid-read readiness of the complete adder

The repair tail introduces no physical outcome. All paid phases read the
complete bank left by the preceding increasing-index streaming vents.
Thus no initial bank-value condition is imposed on caller Stores
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma phase_map_indices {records : Nat}
    (pairs : List (EncodedBit encoding × Fin records)) :
    ventIndices (pairs.map fun pair => .phase pair.1 pair.2) = [] := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => exact ih

/-- Every literal paid phase reads storage and introduces no physical measurement outcome. -/
lemma phaseWord_ventIndices (layout : Layout encoding width) :
    ventIndices layout.phaseWord = [] := by
  have actual := phase_map_indices (List.ofFn fun index : Fin (width - 2) =>
    (layout.dirty index, index))
  simpa only [phaseWord, List.map_ofFn, Function.comp_def] using actual

/-- The actual native/phase/carry/phase/native repair introduces no physical outcomes. -/
lemma tailWord_ventIndices (layout : Layout encoding width) (constant : BitVec width) :
    ventIndices (layout.tailWord constant) = [] := by
  simp only [tailWord, ventIndices_append, phaseWord_ventIndices, ventIndices,
    List.append_nil]

/-- Every actual adder record cell is measured exactly once in its original increasing order. -/
lemma adderWord_ventIndices (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    ventIndices (layout.adderWord wide constant) =
      List.ofFn (fun record : Fin (width - 2) => record) := by
  rw [adderWord_eq_stream_tail, ventIndices_append, tailWord_ventIndices, List.append_nil,
    streamingWord_ventIndices]

/-- Every paid phase in the complete actual adder reads a preceding physical measurement. -/
lemma adderWord_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    ReadyWord (fun _ => False) (layout.adderWord wide constant) := by
  rw [adderWord_eq_stream_tail, readyWord_append]
  refine ⟨readyWord_of_phaseFree _ _ (streamingWord_phaseFree layout wide constant), ?_⟩
  apply readyWord_of_all
  intro record
  rw [availableAfter_iff, streamingWord_ventIndices]
  exact Or.inl (List.mem_ofFn.mpr ⟨record, rfl⟩)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
