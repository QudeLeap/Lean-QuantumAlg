/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Circuit
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Composition
import Mathlib.Algebra.BigOperators.Fin

/-!
# Paid phase cancellation around the actual native dirty carry word

Both phase passes are compiled selected native Z instructions. The carry
word between them is the actual recursively compiled native word. Their
exact retained product depends only on the original source/control carries;
every arbitrary original dirty bit cancels [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction EncodedBit
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual paid phase pass preserves every original encoded bit. -/
lemma phaseWord_label (layout : Layout encoding width) (state : Data) :
    wordLabel layout.phaseWord state = state := by
  simpa only [phaseWord, List.map_ofFn, Function.comp_def] using
    wordLabel_phase_map (List.ofFn fun index : Fin (width - 2) =>
      (layout.dirty index, index)) state

/-- Every selected native Z reads its matching arbitrary original dirty bit. -/
lemma phaseWord_weight (layout : Layout encoding width)
    (outcome : Fin (width - 2) → Fin 2) (state : Data) :
    wordWeight outcome layout.phaseWord state =
      ∏ index, MeasuredUncompute.character (outcome index) ((layout.dirty index).get state) := by
  simpa only [phaseWord, List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    wordWeight_phase_map outcome (List.ofFn fun index : Fin (width - 2) =>
      (layout.dirty index, index)) state

/-- Both actual selected phase passes leave exactly the actual native carry label action. -/
lemma phaseCarry_label (layout : Layout encoding width) (constant : BitVec (width - 2))
    (state : Data) :
    wordLabel (layout.phaseWord ++
      [.native (layout.carryLayout.gates constant)] ++ layout.phaseWord) state =
      GateSpec.stepList (layout.carryLayout.gates constant) state := by
  rw [wordLabel_append, wordLabel_append]
  simp only [phaseWord_label, wordLabel, labelStep]

/-- The two paid dirty phases cancel every unknown dirty value exactly. -/
lemma phaseCarry_weight (layout : Layout encoding width) (constant : BitVec (width - 2))
    (outcome : Fin (width - 2) → Fin 2) (state : Data) :
    wordWeight outcome (layout.phaseWord ++
      [.native (layout.carryLayout.gates constant)] ++ layout.phaseWord) state =
      ∏ index, MeasuredUncompute.character (outcome index)
        (layout.carryLayout.carryValues constant state (index.val + 1)) := by
  rw [wordWeight_append, wordWeight_append]
  simp only [wordLabel_append, phaseWord_label, wordWeight, branchWeight,
    wordLabel, labelStep, mul_one]
  rw [phaseWord_weight, phaseWord_weight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  have actual := CarryLayout.gates_output_get layout.carryLayout constant state index
  change (layout.dirty index).get (GateSpec.stepList (layout.carryLayout.gates constant) state) =
    ((layout.dirty index).get state ^^
      layout.carryLayout.carryValues constant state (index.val + 1)) at actual
  rw [actual, mul_comm]
  exact dirty_phase_cancel (outcome index) ((layout.dirty index).get state)
    (layout.carryLayout.carryValues constant state (index.val + 1))

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
