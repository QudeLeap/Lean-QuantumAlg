/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics

/-!
# Optional result of the actual first-accepted selector

The two persistent latches encode an optional word. The actual Boolean writes
and selected copy arm retain the first eligible candidate, including when the
two scratch references name the same cell.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Decode the existing persistent latch and selected word without allocating storage. -/
def selectedOption (refs : Refs ctx width) (store : Store ctx) : Option (CShape.Word width) :=
  if (store.read (cellRead refs.accepted)).toBool then
    some (store.read (cellRead refs.selected)) else none

/-- Decode the supplied candidate and its existing eligibility cell. -/
def candidateOption (inputs : Inputs ctx width) (store : Store ctx) : Option (CShape.Word width) :=
  if (store.read inputs.eligible).toBool then
    some (store.read inputs.candidate) else none

/-- Keep the first result, using the current candidate only while selection is empty. -/
def retainFirst {α : Type} (previous current : Option α) : Option α :=
  match previous with
  | some value => some value
  | none => current

/-- Actual selection realizes the ordered first-success update of its existing output cells. -/
theorem firstAccepted_selectedOption (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separated : Separated inputs refs) (store : Store ctx) :
    selectedOption refs (step inputs refs store).1 =
      retainFirst (selectedOption refs store) (candidateOption inputs store) := by
  obtain ⟨accepted, selected⟩ := firstAccepted_latches inputs refs separated store
  unfold selectedOption candidateOption
  rw [accepted, selected]
  cases old : (store.read (cellRead refs.accepted)).toBool <;>
    cases eligible : (store.read inputs.eligible).toBool <;>
    simp [retainFirst]

end QuantumAlg.ClassicalRoutines.FirstAccepted
