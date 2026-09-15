/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow.Readout
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Complete preservation through actual narrowing and selection

The temporary resize word is a real lexical allocation. Apart from the four
original writable selector cells, every caller read survives its allocation,
conversion, conditional copies and release. The complete borrowed interface
is restored jointly with every external reference, including correlations
with arbitrary original classical values and borrowed quantum systems.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- All old reads outside the selector's four writable cells retain their complete values. -/
theorem nativeQuadratic_narrow_read_other (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (availableFree : original.available.key ∉ other.storageKeys)
    (takeFree : original.take.key ∉ other.storageKeys)
    (acceptedFree : original.accepted.key ∉ other.storageKeys)
    (selectedFree : original.selected.key ∉ other.storageKeys) (store : Store ctx) :
    (step eligible candidate original store).1.read other = store.read other := by
  let entered := store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
  let resized := entered.applyOp (resizeOp candidate width)
  let selected := (FirstAccepted.step (inputs eligible width) (refs original) resized).1
  have keyEquation : (underRead other width).storageKeys = other.storageKeys :=
    CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh
  have actual := FirstAccepted.firstAccepted_read_other (inputs eligible width) (refs original)
    (underRead other width)
    (keyEquation.symm ▸ availableFree) (keyEquation.symm ▸ takeFree)
    (keyEquation.symm ▸ acceptedFree) (keyEquation.symm ▸ selectedFree) resized
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh selected other).trans
    (actual.trans ((nativeQuadratic_narrow_resize_read_original candidate other width
      entered).trans (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh other)))

/-- The actual scoped conversion and selector restore every full borrowed joint state. -/
theorem nativeQuadratic_narrow_borrowedRestored (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code eligible candidate original).BorrowedRestored Reference state
      ((code eligible candidate original).execute Reference state) := by
  apply Circuit.borrowedRestored_workspace
  intro history historyFinite entered
  exact Circuit.borrowedRestored_seq (.classical (resizeOp candidate width))
    (FirstAccepted.circuit (inputs eligible width) (refs original)) entered
    (Circuit.borrowedRestored_classical (resizeOp candidate width) entered)
    (FirstAccepted.firstAccepted_borrowedRestored
      (inputs eligible width) (refs original) Reference _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection
