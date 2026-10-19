/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics

/-!
# Persistent latch values after actual narrowing and selection

The new resize word cannot overwrite any old input or latch. The existing
first-accepted semantics therefore apply to its actual converted word and
the original eligibility bit. An already accepted factor remains untouched;
otherwise the first eligible candidate is copied at the output width. All
nonaliasing facts below describe internal selector positions supplied by the
enclosing actual layout, not input-value or initialization promises.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The existing selector positions are distinct where actual latch semantics require it. -/
structure Separated (eligible : CInputRef ctx .bit) (original : FirstAccepted.Refs ctx width) :
    Prop where
  availableEligible : original.available.key ∉ eligible.storageKeys
  availableAccepted : original.available.key ≠ original.accepted.key
  takeAccepted : original.take.key ≠ original.accepted.key
  availableSelected : original.available.key ≠ original.selected.key
  takeSelected : original.take.key ≠ original.selected.key
  acceptedSelected : original.accepted.key ≠ original.selected.key

private lemma original_ne_fresh {shape : CShape} (output : CWriteRef ctx shape) :
    output.key ≠ ctx.canonicalFreshKey := by
  intro same
  have original : output.key ∈ ctx.keys :=
    (CInputRef.storage output.toCStorageRef).storageKeys_subset_context
      (List.mem_singleton.mpr rfl)
  exact ctx.canonicalFreshKey_fresh (same ▸ original)

/-- Fresh allocation discharges both candidate/scratch distinctions of the actual selector. -/
lemma nativeQuadratic_narrow_separated (eligible : CInputRef ctx .bit)
    (original : FirstAccepted.Refs ctx width) (separated : Separated eligible original) :
    FirstAccepted.Separated (inputs eligible width) (refs original) where
  availableEligible := by
    change original.available.key ∉
      (eligible.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh).storageKeys
    rw [CInputRef.storageKeys_underWorkspace]
    exact separated.availableEligible
  availableCandidate := fun present => original_ne_fresh original.available
    (List.mem_singleton.mp present)
  takeCandidate := fun present => original_ne_fresh original.take (List.mem_singleton.mp present)
  availableAccepted := separated.availableAccepted
  takeAccepted := separated.takeAccepted
  availableSelected := separated.availableSelected
  takeSelected := separated.takeSelected
  acceptedSelected := separated.acceptedSelected

/-- Actual narrowing changes no original structural read, whatever value the new word receives. -/
lemma nativeQuadratic_narrow_resize_read_original
    (candidate : CInputRef ctx (.unsignedWord sourceWidth)) {shape : CShape}
    (other : CInputRef ctx shape) (width : Nat) (store : Store (context ctx width)) :
    (store.applyOp (resizeOp candidate width)).read (underRead other width) =
      store.read (underRead other width) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  change ctx.canonicalFreshKey ∉
    (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).storageKeys
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

/-- The actual temporary word holds exactly the source word reduced to the target capacity. -/
lemma nativeQuadratic_narrow_resize_read (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (width : Nat) (store : Store (context ctx width)) :
    (store.applyOp (resizeOp candidate width)).read
        (.storage (temporary ctx width).toCStorageRef) =
      CShape.wordOfNat width (store.read (underRead candidate width)).toNat :=
  Store.read_applyOp_output store (resizeOp candidate width)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Narrowing never overwrites an earlier factor; otherwise the actual first eligible word wins. -/
lemma nativeQuadratic_narrow_latches (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) (separated : Separated eligible original)
    (store : Store ctx) :
    let final := (step eligible candidate original store).1
    (final.read (FirstAccepted.cellRead original.accepted)).toBool =
        ((store.read (FirstAccepted.cellRead original.accepted)).toBool ||
          (store.read eligible).toBool) ∧
      final.read (FirstAccepted.cellRead original.selected) =
        if (!(store.read (FirstAccepted.cellRead original.accepted)).toBool) &&
            (store.read eligible).toBool then
          CShape.wordOfNat width (store.read candidate).toNat
        else store.read (FirstAccepted.cellRead original.selected) := by
  let entered : Store (context ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let resized : Store (context ctx width) := entered.applyOp (resizeOp candidate width)
  let selected : Store (context ctx width) :=
    (FirstAccepted.step (inputs eligible width) (refs original) resized).1
  have oldRead {shape : CShape} (other : CInputRef ctx shape) :
      resized.read (underRead other width) = store.read other :=
    (nativeQuadratic_narrow_resize_read_original candidate other width entered).trans
      (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh other)
  have eligibleValue : resized.read (inputs eligible width).eligible = store.read eligible :=
    oldRead eligible
  have acceptedValue : resized.read (FirstAccepted.cellRead (refs original).accepted) =
      store.read (FirstAccepted.cellRead original.accepted) :=
    oldRead (FirstAccepted.cellRead original.accepted)
  have selectedValue : resized.read (FirstAccepted.cellRead (refs original).selected) =
      store.read (FirstAccepted.cellRead original.selected) :=
    oldRead (FirstAccepted.cellRead original.selected)
  have candidateValue : resized.read (inputs eligible width).candidate =
      CShape.wordOfNat width (store.read candidate).toNat :=
    (nativeQuadratic_narrow_resize_read candidate width entered).trans
      (congrArg (fun value : CShape.Value (.unsignedWord sourceWidth) =>
        CShape.wordOfNat width value.toNat)
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
          (.unsignedWord width) ctx.canonicalFreshKey_fresh candidate))
  have actual := FirstAccepted.firstAccepted_latches (model := model)
    (inputs eligible width) (refs original)
    (nativeQuadratic_narrow_separated eligible original separated) resized
  have acceptedExit := congrArg CShape.Value.toBool
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh selected (FirstAccepted.cellRead original.accepted))
  have selectedExit := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh selected
    (FirstAccepted.cellRead original.selected)
  refine ⟨acceptedExit.trans (actual.1.trans ?_), selectedExit.trans (actual.2.trans ?_)⟩
  · exact congrArg₂ (fun (accepted eligible : CShape.Value .bit) =>
      accepted.toBool || eligible.toBool) acceptedValue eligibleValue
  · exact congrArg₂
      (fun (flags : CShape.Value .bit × CShape.Value .bit)
          (words : CShape.Value (.unsignedWord width) × CShape.Value (.unsignedWord width)) =>
        if (!flags.1.toBool) && flags.2.toBool then words.1 else words.2)
      (congrArg₂ (fun (left right : CShape.Value .bit) => (left, right))
        acceptedValue eligibleValue)
      (congrArg₂ (fun (left right : CShape.Value (.unsignedWord width)) => (left, right))
        candidateValue selectedValue)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection
