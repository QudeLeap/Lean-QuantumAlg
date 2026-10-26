/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Readiness
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Literal record indices and source-order availability of paid phase inputs

Availability advances only at an actual physical vent. Its composition law
retains the exact chronological instruction order. The physical write list
has these same indices for every actual outcome family
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {ctx : RuntimeCtx .quantum}

/-- Exactly the destination indices of the literal physical vents, in source order. -/
def ventIndices : List (Instruction encoding records) → List (Fin records)
  | [] => []
  | .native _ :: rest => ventIndices rest
  | .vent _ record :: rest => record :: ventIndices rest
  | .phase _ _ :: rest => ventIndices rest

/-- The cells actually available after executing precisely the supplied instruction prefix. -/
def availableAfter : (Fin records → Prop) → List (Instruction encoding records) →
    Fin records → Prop
  | ready, [] => ready
  | ready, .native _ :: rest => availableAfter ready rest
  | ready, .vent _ record :: rest =>
      availableAfter (fun index => index = record ∨ ready index) rest
  | ready, .phase _ _ :: rest => availableAfter ready rest

/-- Availability is exactly the supplied initial set together with actual preceding vent writes. -/
lemma availableAfter_iff (ready : Fin records → Prop)
    (word : List (Instruction encoding records)) (index : Fin records) :
    availableAfter ready word index ↔ index ∈ ventIndices word ∨ ready index := by
  induction word generalizing ready with
  | nil => simp only [availableAfter, ventIndices, List.not_mem_nil, false_or]
  | cons instruction rest ih =>
      cases instruction with
      | native gates => exact ih ready
      | vent target record =>
          rw [availableAfter, ih, ventIndices, List.mem_cons]
          tauto
      | phase target record => exact ih ready

/-- Concatenation preserves the actual cell-availability boundary between both source words. -/
lemma readyWord_append (ready : Fin records → Prop)
    (first second : List (Instruction encoding records)) :
    ReadyWord ready (first ++ second) ↔
      ReadyWord ready first ∧ ReadyWord (availableAfter ready first) second := by
  induction first generalizing ready with
  | nil => simp only [List.nil_append, ReadyWord, availableAfter, true_and]
  | cons instruction rest ih =>
      cases instruction with
      | native gates => exact ih ready
      | vent target record => exact ih (fun index => index = record ∨ ready index)
      | phase target record =>
          simp only [List.cons_append, ReadyWord, availableAfter, ih, and_assoc]

/-- Actual physical writes use the literal vent indices for every original Store. -/
lemma outcomeWrites_indices (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    ∀ (word : List (Instruction encoding records))
      (measured : WordOutcomes physical sameWires word),
    (outcomeWrites physical sameWires word measured).map Prod.fst = ventIndices word := by
  intro word
  induction word with
  | nil => intro measured; rfl
  | cons instruction rest ih =>
      intro measured
      cases instruction with
      | native gates => exact ih measured.2
      | vent target record =>
          change record :: (outcomeWrites physical sameWires rest measured.2).map Prod.fst =
            record :: ventIndices rest
          rw [ih]
      | phase target record => exact ih measured.2

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
