/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Persistent.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Values
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program.Checked

/-!
# Source-correct update of the original persistent factor latches

The actual arithmetic and both checks establish the source candidates and
their complete nontrivial-divisor tests. The actual local selector picks the
first valid candidate. Narrowing then updates the original persistent cells:
an earlier accepted factor remains unchanged; otherwise the first valid
source factor is stored at the declared output width. No candidate fit or
initial-value condition is assumed; the real width conversion is explicit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open Execution
open ClassicalRoutines

variable {width resultWidth : Nat}

private theorem latch_replace
    {accepted eligible sourceAccepted sourceEligible : Bool}
    {old sourceOld : CShape.Value (.unsignedWord resultWidth)} {candidate sourceCandidate : Nat}
    (acceptedEq : accepted = sourceAccepted) (eligibleEq : eligible = sourceEligible)
    (oldEq : old = sourceOld) (candidateEq : candidate = sourceCandidate) :
    (if (!accepted) && eligible then CShape.wordOfNat resultWidth candidate else old) =
      if (!sourceAccepted) && sourceEligible then
        CShape.wordOfNat resultWidth sourceCandidate else sourceOld := by
  cases acceptedEq
  cases eligibleEq
  cases oldEq
  cases candidateEq
  rfl

private theorem latch_order (accepted firstValid secondValid : Bool) (first second : Nat)
    (old : CShape.Value (.unsignedWord resultWidth)) :
    (if (!accepted) && (firstValid || secondValid) then
      CShape.wordOfNat resultWidth (if firstValid then first else if secondValid then second else 0)
    else old) =
      if accepted then old else if firstValid then CShape.wordOfNat resultWidth first
      else if secondValid then CShape.wordOfNat resultWidth second else old := by
  cases accepted <;> cases firstValid <;> cases secondValid <;> rfl

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private theorem checked_store_projection
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (store : Store (context ctx width)) :
    (checkedBodyStep (model := model) (ctx := ctx) (width := width) modulus original store).1 =
      (NarrowSelection.step (model := model)
        (FirstAccepted.cellRead (pairRefs modulus).selection.accepted)
        (FirstAccepted.cellRead (pairRefs modulus).selection.selected)
        (persistentRefs original width)
        (Pair.step (model := model) (pairRefs modulus) store).1).1 := rfl

set_option maxHeartbeats 800000 in -- Instantiate source and read laws for thirteen actual cells.
/-- Actual checking and narrowing implement source priority in the same original persistent cells.
-/
theorem nativeQuadratic_persistent_checked_values
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
    let final := (checkedBodyStep (model := model) modulus original
      (CheckLayout.pushStore (RSA.quadraticWordWidth width)
        (initializedStore (model := model) input modulus store))).1
    (final.read (FirstAccepted.cellRead (persistentRefs original width).accepted)).toBool =
        ((store.read (FirstAccepted.cellRead original.accepted)).toBool ||
          (firstValid || secondValid)) ∧
      final.read (FirstAccepted.cellRead (persistentRefs original width).selected) =
        if (store.read (FirstAccepted.cellRead original.accepted)).toBool then
          store.read (FirstAccepted.cellRead original.selected)
        else if firstValid then CShape.wordOfNat resultWidth source.1
        else if secondValid then CShape.wordOfNat resultWidth source.2
        else store.read (FirstAccepted.cellRead original.selected) := by
  let entered : Store (context ctx width) :=
    CheckLayout.pushStore (RSA.quadraticWordWidth width)
      (initializedStore (model := model) input modulus store)
  let paired : Store (context ctx width) :=
    (Pair.step (model := model) (pairRefs modulus) entered).1
  have localValues := nativeQuadratic_local_pair_values (model := model) input modulus store
  have acceptedRead : paired.read
      (FirstAccepted.cellRead (persistentRefs original width).accepted) =
        store.read (FirstAccepted.cellRead original.accepted) :=
    (congrArg (fun ref : CInputRef (context ctx width) .bit => paired.read ref)
      (nativeQuadratic_persistent_underWrite_read original.accepted width)).trans
      (nativeQuadratic_persistent_checked_entry_read (model := model) input modulus
        (FirstAccepted.cellRead original.accepted) store)
  have selectedRead : paired.read
      (FirstAccepted.cellRead (persistentRefs original width).selected) =
        store.read (FirstAccepted.cellRead original.selected) :=
    (congrArg (fun ref : CInputRef (context ctx width) (.unsignedWord resultWidth) =>
      paired.read ref)
      (nativeQuadratic_persistent_underWrite_read original.selected width)).trans
      (nativeQuadratic_persistent_checked_entry_read (model := model) input modulus
        (FirstAccepted.cellRead original.selected) store)
  have actual := NarrowSelection.nativeQuadratic_narrow_latches (model := model)
    (FirstAccepted.cellRead (pairRefs modulus).selection.accepted)
    (FirstAccepted.cellRead (pairRefs modulus).selection.selected)
    (persistentRefs original width) (nativeQuadratic_persistent_narrow_separated
      modulus original unique) paired
  have finalStore := checked_store_projection (model := model) modulus original entered
  have acceptedAfter := congrArg (fun current : Store (context ctx width) =>
    (current.read (FirstAccepted.cellRead (persistentRefs original width).accepted)).toBool)
    finalStore
  have selectedAfter := congrArg (fun current : Store (context ctx width) =>
    current.read (FirstAccepted.cellRead (persistentRefs original width).selected)) finalStore
  refine ⟨acceptedAfter.trans (actual.1.trans ?_), selectedAfter.trans (actual.2.trans ?_)⟩
  · exact congrArg₂ Bool.or (congrArg CShape.Value.toBool acceptedRead) localValues.1
  · exact (latch_replace (congrArg CShape.Value.toBool acceptedRead)
      localValues.1 selectedRead localValues.2).trans (latch_order _ _ _ _ _ _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
