/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program.Execution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Persistent.Values

/-!
# Original persistent source values after all actual scope releases

The final readout is obtained from the same complete native program update.
All thirteen local cells have been released. The original acceptance flag
and output word still implement earlier-result preservation and the source's
first-valid quadratic candidate order. The concrete allocated-selector
version discharges all positional facts with its actual layout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

private theorem candidate_store_projection
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (store : Store (LocalLayout.candidateContext ctx width)) :
    (candidateBodyStep input modulus original store).1 =
      (CheckLayout.scopeStep (RSA.quadraticWordWidth width)
        (checkedBody modulus original) (checkedBodyStep modulus original)
        (Initialized.step (LocalLayout.arithmeticRead input width)
          (LocalLayout.arithmeticRead modulus width)
          (LocalLayout.arithmeticRefs ctx width) store).1).1 := rfl

set_option maxHeartbeats 800000 in -- Transport an actual store projection through five scopes.
/-- The checker release exposes the same surviving original reads of the actual checked body. -/
theorem nativeQuadratic_candidateBodyStep_read
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) {shape : CShape}
    (other : CInputRef ctx shape) (store : Store (LocalLayout.candidateContext ctx width)) :
    (candidateBodyStep input modulus original store).1.read
        (LocalLayout.arithmeticRead other width) =
      (checkedBodyStep modulus original (CheckLayout.pushStore (RSA.quadraticWordWidth width)
        (Initialized.step (LocalLayout.arithmeticRead input width)
          (LocalLayout.arithmeticRead modulus width)
          (LocalLayout.arithmeticRefs ctx width) store).1)).1.read
        (LocalLayout.underRead other width) := by
  have released := CheckLayout.nativeQuadratic_checkScopeStep_store
    (RSA.quadraticWordWidth width) (checkedBody modulus original)
    (checkedBodyStep modulus original)
    (Initialized.step (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width) store).1
  have finalStore := (candidate_store_projection input modulus original store).trans released
  exact (congrArg (fun current : Store (LocalLayout.candidateContext ctx width) =>
    current.read (LocalLayout.arithmeticRead other width)) finalStore).trans
    (CheckLayout.nativeQuadratic_checkLayout_pop_read
      (LocalLayout.arithmeticRead other width) (RSA.quadraticWordWidth width) _)

set_option maxHeartbeats 800000 in -- Transport both real latch references across thirteen cells.
/-- The same actual returned store has the original first-factor acceptance and payload. -/
theorem nativeQuadratic_program_latches
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (unique : ([original.take.key, original.available.key, original.selected.key,
      original.accepted.key] : List StorageKey).Nodup) (store : Store ctx) :
    let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
    let firstValid := decide (1 < source.1 ∧ source.1 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.1 = 0)
    let secondValid := decide (1 < source.2 ∧ source.2 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.2 = 0)
    let final := (programStep input modulus original store).1
    (final.read (FirstAccepted.cellRead original.accepted)).toBool =
        ((store.read (FirstAccepted.cellRead original.accepted)).toBool ||
          (firstValid || secondValid)) ∧
      final.read (FirstAccepted.cellRead original.selected) =
        if (store.read (FirstAccepted.cellRead original.accepted)).toBool then
          store.read (FirstAccepted.cellRead original.selected)
        else if firstValid then CShape.wordOfNat resultWidth source.1
        else if secondValid then CShape.wordOfNat resultWidth source.2
        else store.read (FirstAccepted.cellRead original.selected) := by
  let checked : Store (LocalLayout.context ctx width) :=
    (checkedBodyStep modulus original
      (CheckLayout.pushStore (RSA.quadraticWordWidth width)
        (LocalLayout.initializedStore input modulus store))).1
  have acceptedExit := (nativeQuadratic_programStep_read input modulus original
    (FirstAccepted.cellRead original.accepted) store).trans
    (nativeQuadratic_candidateBodyStep_read input modulus original
      (FirstAccepted.cellRead original.accepted) (LocalLayout.entryStore width store))
  have selectedExit := (nativeQuadratic_programStep_read input modulus original
    (FirstAccepted.cellRead original.selected) store).trans
    (nativeQuadratic_candidateBodyStep_read input modulus original
      (FirstAccepted.cellRead original.selected) (LocalLayout.entryStore width store))
  have actual := LocalLayout.nativeQuadratic_persistent_checked_values
    input modulus original unique store
  have acceptedReference := congrArg (fun ref : CInputRef (LocalLayout.context ctx width) .bit =>
    checked.read ref)
    (LocalLayout.nativeQuadratic_persistent_underWrite_read original.accepted width).symm
  have selectedReference := congrArg
    (fun ref : CInputRef (LocalLayout.context ctx width) (.unsignedWord resultWidth) =>
      checked.read ref)
    (LocalLayout.nativeQuadratic_persistent_underWrite_read original.selected width).symm
  exact ⟨(congrArg CShape.Value.toBool (acceptedExit.trans acceptedReference)).trans actual.1,
    (selectedExit.trans selectedReference).trans actual.2⟩

/-- An actual persistent-selector allocation satisfies the complete source contract without
caller initialization, aliasing, quantum-absence or candidate-capacity premises. -/
theorem nativeQuadratic_allocated_program_latches
    (input : CInputRef (SelectionLayout.context ctx resultWidth) (.unsignedWord width))
    (modulus : CInputRef (SelectionLayout.context ctx resultWidth)
      (.unsignedWord (RSA.quadraticWordWidth width)))
    (store : Store (SelectionLayout.context ctx resultWidth)) :
    let original := SelectionLayout.refs ctx resultWidth
    let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
    let firstValid := decide (1 < source.1 ∧ source.1 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.1 = 0)
    let secondValid := decide (1 < source.2 ∧ source.2 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.2 = 0)
    let final := (programStep input modulus original store).1
    (final.read (FirstAccepted.cellRead original.accepted)).toBool =
        ((store.read (FirstAccepted.cellRead original.accepted)).toBool ||
          (firstValid || secondValid)) ∧
      final.read (FirstAccepted.cellRead original.selected) =
        if (store.read (FirstAccepted.cellRead original.accepted)).toBool then
          store.read (FirstAccepted.cellRead original.selected)
        else if firstValid then CShape.wordOfNat resultWidth source.1
        else if secondValid then CShape.wordOfNat resultWidth source.2
        else store.read (FirstAccepted.cellRead original.selected) :=
  nativeQuadratic_program_latches input modulus (SelectionLayout.refs ctx resultWidth)
    (SelectionLayout.nativeRecovery_selection_nodup ctx resultWidth) store

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
