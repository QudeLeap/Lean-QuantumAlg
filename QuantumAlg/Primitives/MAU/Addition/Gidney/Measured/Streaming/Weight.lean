/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Rows
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact retained vent factors of the actual chronological streaming word

There is one physical vent for each original carry except the final one.
The product retains the original-carry character of every actual outcome,
including when the coherent quantum control is false. No normalized branch
mass is inferred without the remaining complete-instrument and graph laws
[G25, main.tex:199-251,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- A chronological row prefix has exactly its actual original-carry vent-factor product. -/
lemma streamingRows_weight (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (outcome : Fin (width - 2) → Fin 2) (count : Nat) (bounded : count ≤ width - 1) :
    wordWeight outcome (layout.streamingRows wide constant count bounded)
        (stepList (layout.offsetGates constant) initial) =
      (List.ofFn fun record : Fin (count - 1) =>
        NormalizedVector.invSqrt2 * MeasuredUncompute.character
          (outcome ⟨record.val, by omega⟩)
          (layout.carryInto constant initial (record.val + 1))).prod := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows_weight_succ, ih (by omega)]
      have invariant := streamingRows_prefixInvariant layout wide constant initial clean
        count (by omega : count ≤ width - 2)
      rw [prefixInvariant_incoming_helper invariant]
      cases count with
      | zero =>
          rw [dif_neg (by omega : ¬ 0 < 0)]
          simp only [List.ofFn_zero, List.prod_nil, mul_one]
      | succ count =>
          rw [dif_pos (Nat.succ_pos count), List.ofFn_succ', List.prod_concat]
          rfl

/-- The complete actual streaming word has one common magnitude and the original carry sign. -/
lemma streamingWord_weight (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (outcome : Fin (width - 2) → Fin 2) :
    wordWeight outcome (layout.streamingWord wide constant) initial =
      NormalizedVector.invSqrt2 ^ (width - 2) *
        ∏ record : Fin (width - 2), MeasuredUncompute.character (outcome record)
          (layout.carryInto constant initial (record.val + 1)) := by
  rw [streamingWord_eq_rows]
  change 1 * wordWeight outcome (layout.streamingRows wide constant (width - 1) le_rfl)
    (stepList (layout.offsetGates constant) initial) = _
  rw [one_mul]
  have actual := streamingRows_weight layout wide constant initial clean outcome
    (width - 1) le_rfl
  have countEq : width - 1 - 1 = width - 2 := by omega
  rw [List.ofFn_congr countEq, List.prod_ofFn, Finset.prod_mul_distrib] at actual
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.val_cast, Fin.eta]
    using actual

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
