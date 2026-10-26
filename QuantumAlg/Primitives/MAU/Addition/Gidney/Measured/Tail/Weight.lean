/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Arithmetic
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Weight

/-!
# Exact common retained amplitude of the complete measured constant adder

The actual paid phase/carry/phase tail recovers the original carries and
cancels every retained vent character. Its scalar is independent of the
original target, dirty systems, coherent control and measurement outcomes.
Normalization additionally requires the complete actual instrument and
the clean-input isometry [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma character_square (outcome : Fin 2) (bit : Bool) :
    MeasuredUncompute.character outcome bit * MeasuredUncompute.character outcome bit = 1 := by
  by_cases selected : outcome = 1 <;> cases bit <;>
    norm_num [MeasuredUncompute.character, selected]

/-- Every retained record has exactly the same scalar on all admitted full encoded labels. -/
lemma adderWord_weight (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (outcome : Fin (width - 2) → Fin 2) :
    wordWeight outcome (layout.adderWord wide constant) initial =
      NormalizedVector.invSqrt2 ^ (width - 2) := by
  rw [adderWord_eq_stream_tail, wordWeight_append,
    streamingWord_weight layout wide constant initial clean, tailWord_weight]
  change (NormalizedVector.invSqrt2 ^ (width - 2) *
    ∏ index : Fin (width - 2), MeasuredUncompute.character (outcome index)
      (layout.carryInto constant initial (index.val + 1))) *
    (∏ index : Fin (width - 2), MeasuredUncompute.character (outcome index)
      (layout.carryLayout.carryValues (constant.setWidth (width - 2))
        (layout.complementedStream wide constant initial) (index.val + 1))) = _
  have samePhases :
      (∏ index : Fin (width - 2), MeasuredUncompute.character (outcome index)
        (layout.carryLayout.carryValues (constant.setWidth (width - 2))
          (layout.complementedStream wide constant initial) (index.val + 1))) =
      ∏ index : Fin (width - 2), MeasuredUncompute.character (outcome index)
        (layout.carryInto constant initial (index.val + 1)) := by
    apply Finset.prod_congr rfl
    intro index _
    rw [complementedStream_carryValues layout wide constant initial clean _ (by omega)]
  rw [samePhases, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [character_square, Finset.prod_const_one, mul_one]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
