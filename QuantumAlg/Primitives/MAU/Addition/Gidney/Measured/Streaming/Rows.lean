/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Readout
import Mathlib.Data.List.OfFn

/-!
# Chronological prefixes of the same actual measured streaming word

The recursion appends the next original indexed row. Its full prefix is the
literal existing streaming word, preserving the source row order and every
physical vent [G25, main.tex:209-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The first specified number of actual source rows in increasing bit order. -/
def streamingRows (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    (count : Nat) → count ≤ width - 1 → List (Instruction encoding (width - 2))
  | 0, _ => []
  | count + 1, bounded =>
      layout.streamingRows wide constant count (by omega) ++
        layout.streamingStep wide constant ⟨count, by omega⟩

/-- Each prefix is exactly the original finite list of the same addressed rows. -/
lemma streamingRows_eq_ofFn (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    layout.streamingRows wide constant count bounded =
      (List.ofFn fun index : Fin count =>
        layout.streamingStep wide constant ⟨index.val, by omega⟩).flatten := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [ih]
      rfl

/-- The complete chronological prefix is the literal existing source streaming word. -/
lemma streamingWord_eq_rows (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    layout.streamingWord wide constant =
      .native (layout.offsetGates constant) ::
        layout.streamingRows wide constant (width - 1) le_rfl := by
  rw [streamingRows_eq_ofFn]
  rfl

/-- The next actual row acts on the complete label left by the earlier chronological rows. -/
lemma streamingRows_label_succ (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count + 1 ≤ width - 1)
    (state : Data) :
    wordLabel (layout.streamingRows wide constant (count + 1) bounded) state =
      wordLabel (layout.streamingStep wide constant ⟨count, by omega⟩)
        (wordLabel (layout.streamingRows wide constant count (by omega)) state) := by
  rw [streamingRows, wordLabel_append]

/-- The next actual vent factor multiplies the weight on the preceding chronological label. -/
lemma streamingRows_weight_succ (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count + 1 ≤ width - 1)
    (outcome : Fin (width - 2) → Fin 2) (state : Data) :
    wordWeight outcome (layout.streamingRows wide constant (count + 1) bounded) state =
      wordWeight outcome (layout.streamingRows wide constant count (by omega)) state *
        (if positive : 0 < count then
          NormalizedVector.invSqrt2 * EncodedBit.MeasuredUncompute.character
            (outcome ⟨count - 1, by omega⟩)
            ((layout.carryHelper count).get
              (wordLabel (layout.streamingRows wide constant count (by omega)) state))
        else 1) := by
  rw [streamingRows, wordWeight_append, streamingStep_weight]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
