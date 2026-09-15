/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Actual first-success selection without additional scratch
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural input for either actual persistent result cell. -/
abbrev writeInput {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- The two persistent result cells used by first-success selection. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  accepted : CWriteRef ctx .bit
  selected : CWriteRef ctx (.unsignedWord width)

/-- The original two source reads and the distinct persistent destinations cannot interfere. -/
structure Separation (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) : Prop where
  eligibleAvoidsAccepted : refs.accepted.key ∉ eligible.storageKeys
  eligibleAvoidsSelected : refs.selected.key ∉ eligible.storageKeys
  candidateAvoidsAccepted : refs.accepted.key ∉ candidate.storageKeys
  candidateAvoidsSelected : refs.selected.key ∉ candidate.storageKeys
  acceptedNeSelected : refs.accepted.key ≠ refs.selected.key

/-- Actual reads outside the two persistent destinations constitute the complete caller frame. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.accepted.key ∉ other.storageKeys → refs.selected.key ∉ other.storageKeys →
      after.read other = before.read other

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
