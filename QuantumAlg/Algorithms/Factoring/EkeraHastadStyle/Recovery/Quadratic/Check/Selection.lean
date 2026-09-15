/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Values

/-!
# Real selector positions below the checker cells

Both stored validity bits are fresh checker outputs. The existing selector
cells remain their original writable positions beneath these five cells.
The internal separation facts below are solely relations among those actual
positions and the two original candidate reads; the enclosing fresh layouts
supply them without any additional condition on input values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Internal live-range distinctions for the actual old selector and candidate words. -/
structure SelectorSeparated (inputs : Operands ctx width) : Prop where
  /-- Selector instructions preserve both candidate words until their possible copies. -/
  candidateFree : ∀ key ∈ [inputs.selection.available.key, inputs.selection.take.key,
    inputs.selection.accepted.key, inputs.selection.selected.key],
    key ∉ inputs.first.storageKeys ∧ key ∉ inputs.second.storageKeys
  /-- The real remainder writes preserve the existing acceptance latch. -/
  remainderAccepted : inputs.remainder.key ≠ inputs.selection.accepted.key
  /-- The real remainder writes preserve the existing selected word. -/
  remainderSelected : inputs.remainder.key ≠ inputs.selection.selected.key
  /-- The actual selector's two scratch bits are separate from its two latches. -/
  availableAccepted : inputs.selection.available.key ≠ inputs.selection.accepted.key
  takeAccepted : inputs.selection.take.key ≠ inputs.selection.accepted.key
  availableSelected : inputs.selection.available.key ≠ inputs.selection.selected.key
  takeSelected : inputs.selection.take.key ≠ inputs.selection.selected.key
  acceptedSelected : inputs.selection.accepted.key ≠ inputs.selection.selected.key

private theorem lifted_free {shape : CShape} (output : CWriteRef ctx shape)
    {inputShape : CShape} (input : CInputRef ctx inputShape) (width : Nat)
    (free : output.key ∉ input.storageKeys) :
    (underWrite output width).key ∉ (underRead input width).storageKeys := by
  rw [nativeQuadratic_checkLayout_underWrite_key, nativeQuadratic_checkLayout_underRead_keys]
  exact free

private theorem valid_free {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) (valid : CWriteRef (context ctx width) .bit)
    (internal : valid.key ∈ internalKeys ctx width) :
    (underWrite output width).key ∉ (CInputRef.storage valid.toCStorageRef).storageKeys :=
  fun present => nativeQuadratic_checkLayout_original_ne output width valid.key internal
    (List.mem_singleton.mp present)

/-- Fresh checker outputs and actual candidate separation satisfy both ordered selectors. -/
theorem nativeQuadratic_checked_selection_separated (inputs : Operands ctx width)
    (separated : SelectorSeparated inputs) :
    Selection.Separated (Pair.selectedInputs (pairRefs inputs).first)
      (Pair.selectedInputs (pairRefs inputs).second) (pairRefs inputs).selection where
  firstSeparated := {
    availableEligible := valid_free inputs.selection.available width (firstValid ctx width)
      (by simp [internalKeys])
    availableCandidate := lifted_free inputs.selection.available inputs.first width
      (separated.candidateFree _ (by simp)).1
    takeCandidate := lifted_free inputs.selection.take inputs.first width
      (separated.candidateFree _ (by simp)).1
    availableAccepted := separated.availableAccepted
    takeAccepted := separated.takeAccepted
    availableSelected := separated.availableSelected
    takeSelected := separated.takeSelected
    acceptedSelected := separated.acceptedSelected }
  secondSeparated := {
    availableEligible := valid_free inputs.selection.available width (secondValid ctx width)
      (by simp [internalKeys])
    availableCandidate := lifted_free inputs.selection.available inputs.second width
      (separated.candidateFree _ (by simp)).2
    takeCandidate := lifted_free inputs.selection.take inputs.second width
      (separated.candidateFree _ (by simp)).2
    availableAccepted := separated.availableAccepted
    takeAccepted := separated.takeAccepted
    availableSelected := separated.availableSelected
    takeSelected := separated.takeSelected
    acceptedSelected := separated.acceptedSelected }
  availableEligible := valid_free inputs.selection.available width (secondValid ctx width)
    (by simp [internalKeys])
  takeEligible := valid_free inputs.selection.take width (secondValid ctx width)
    (by simp [internalKeys])
  acceptedEligible := valid_free inputs.selection.accepted width (secondValid ctx width)
    (by simp [internalKeys])
  selectedEligible := valid_free inputs.selection.selected width (secondValid ctx width)
    (by simp [internalKeys])
  availableCandidate := lifted_free inputs.selection.available inputs.second width
    (separated.candidateFree _ (by simp)).2
  takeCandidate := lifted_free inputs.selection.take inputs.second width
    (separated.candidateFree _ (by simp)).2
  acceptedCandidate := lifted_free inputs.selection.accepted inputs.second width
    (separated.candidateFree _ (by simp)).2
  selectedCandidate := lifted_free inputs.selection.selected inputs.second width
    (separated.candidateFree _ (by simp)).2

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
