/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability

/-!
# Source-order record availability for native/vent prefixes and paid tails

These syntactic laws retain every literal instruction. A prefix without phase
reads is ready on an arbitrary original Store. Once all records have been
physically written, every later stored-result phase is ready
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}

/-- The supplied instruction word contains no paid stored-outcome phase read. -/
def PhaseFree : List (Instruction encoding records) → Prop
  | [] => True
  | .native _ :: rest => PhaseFree rest
  | .vent _ _ :: rest => PhaseFree rest
  | .phase _ _ :: _ => False

/-- Literal chronological concatenation concatenates exactly the actual physical vent indices. -/
lemma ventIndices_append (first second : List (Instruction encoding records)) :
    ventIndices (first ++ second) = ventIndices first ++ ventIndices second := by
  induction first with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction <;> simp only [List.cons_append, ventIndices, ih]

/-- Splitting a source word preserves exactly its absence of paid phase reads. -/
lemma phaseFree_append (first second : List (Instruction encoding records)) :
    PhaseFree (first ++ second) ↔ PhaseFree first ∧ PhaseFree second := by
  induction first with
  | nil => simp only [List.nil_append, PhaseFree, true_and]
  | cons instruction rest ih =>
      cases instruction <;> simp only [List.cons_append, PhaseFree, ih, false_and]

/-- A word with no phase read admits an arbitrary original Store and old bank values. -/
lemma readyWord_of_phaseFree (ready : Fin records → Prop)
    (word : List (Instruction encoding records)) (free : PhaseFree word) :
    ReadyWord ready word := by
  induction word generalizing ready with
  | nil => trivial
  | cons instruction rest ih =>
      cases instruction with
      | native gates => exact ih ready free
      | vent target record => exact ih (fun index => index = record ∨ ready index) free
      | phase target record => exact free.elim

/-- Once every bank cell is available, every later literal paid phase read is ready. -/
lemma readyWord_of_all (ready : Fin records → Prop) (allReady : ∀ index, ready index)
    (word : List (Instruction encoding records)) : ReadyWord ready word := by
  induction word generalizing ready with
  | nil => trivial
  | cons instruction rest ih =>
      cases instruction with
      | native gates => exact ih ready allReady
      | vent target record =>
          exact ih (fun index => index = record ∨ ready index)
            (fun index => Or.inr (allReady index))
      | phase target record => exact ⟨allReady record, ih ready allReady⟩

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
