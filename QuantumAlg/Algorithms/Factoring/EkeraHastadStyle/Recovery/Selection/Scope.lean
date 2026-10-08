/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Selection.Layout

/-!
# Actual first-factor scope allocation and entry values

The recovery body executes inside exactly four existing workspace
constructors. Their real pushes supply the clear acceptance latch and zero
selected word. Original parameter and terminal reads are unchanged. Thus
source early-factor priority follows from allocation and actual selector
execution, without an initialization or nonaliasing premise on the caller.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Execute an actual recovery body inside precisely its four lexical selector cells. -/
def scopes {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (width : Nat)
    (body : Circuit model (context ctx width) (context ctx width)) : Circuit model ctx ctx :=
  let takeScope := Circuit.workspace (availableCtx ctx width)
    (availableCtx ctx width).canonicalFreshKey .bit
    (availableCtx ctx width).canonicalFreshKey_fresh body
  let availableScope := Circuit.workspace (selectedCtx ctx width)
    (selectedCtx ctx width).canonicalFreshKey .bit
    (selectedCtx ctx width).canonicalFreshKey_fresh takeScope
  let selectedScope := Circuit.workspace (acceptedCtx ctx)
    (acceptedCtx ctx).canonicalFreshKey (.unsignedWord width)
    (acceptedCtx ctx).canonicalFreshKey_fresh availableScope
  Circuit.workspace ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh selectedScope

/-- Actual store extension in the same order as the four lexical constructors. -/
def pushStore (width : Nat) (store : Store ctx) : Store (context ctx width) :=
  let first := store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let second := first.pushWorkspace (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let third := second.pushWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  third.pushWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh

/-- The same four lexical cells are popped in the reverse of their actual allocation order. -/
def popStore (width : Nat) (store : Store (context ctx width)) : Store ctx :=
  let third := Store.popWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh store
  let second := Store.popWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh third
  let first := Store.popWorkspace (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh second
  Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh first

/-- Entering these actual scopes preserves every original structural input value. -/
theorem nativeRecovery_selection_push_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let first : Store (acceptedCtx ctx) :=
    store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let second : Store (selectedCtx ctx width) :=
    first.pushWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let third : Store (availableCtx ctx width) :=
    second.pushWorkspace (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  let firstRead : CInputRef (acceptedCtx ctx) shape :=
    input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let secondRead : CInputRef (selectedCtx ctx width) shape :=
    firstRead.underWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let thirdRead : CInputRef (availableCtx ctx width) shape :=
    secondRead.underWorkspace (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace third (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh thirdRead).trans
    ((Store.read_pushWorkspace_underWorkspace second (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh secondRead).trans
      ((Store.read_pushWorkspace_underWorkspace first (acceptedCtx ctx).canonicalFreshKey
        (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh firstRead).trans
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey .bit
          ctx.canonicalFreshKey_fresh input)))

/-- Exiting these actual scopes exposes exactly the surviving original entries. -/
theorem nativeRecovery_selection_pop_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let third : Store (availableCtx ctx width) :=
    Store.popWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh store
  let second : Store (selectedCtx ctx width) :=
    Store.popWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh third
  let first : Store (acceptedCtx ctx) :=
    Store.popWorkspace (acceptedCtx ctx).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx).canonicalFreshKey_fresh second
  let firstRead : CInputRef (acceptedCtx ctx) shape :=
    input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let secondRead : CInputRef (selectedCtx ctx width) shape :=
    firstRead.underWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let thirdRead : CInputRef (availableCtx ctx width) shape :=
    secondRead.underWorkspace (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh first input).trans
    ((Store.read_popWorkspace_underWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh second firstRead).trans
      ((Store.read_popWorkspace_underWorkspace (selectedCtx ctx width).canonicalFreshKey
        .bit (selectedCtx ctx width).canonicalFreshKey_fresh third secondRead).trans
        (Store.read_popWorkspace_underWorkspace (availableCtx ctx width).canonicalFreshKey
          .bit (availableCtx ctx width).canonicalFreshKey_fresh store thirdRead)))

/-- The real newly allocated acceptance flag is false. -/
theorem nativeRecovery_selection_push_accepted (width : Nat) (store : Store ctx) :
    (pushStore width store).read (FirstAccepted.cellRead (accepted ctx width)) =
      CShape.Value.bit false := rfl

/-- The real newly allocated selected word is zero at its exact declared width. -/
theorem nativeRecovery_selection_push_selected (width : Nat) (store : Store ctx) :
    (pushStore width store).read (FirstAccepted.cellRead (selected ctx width)) =
      CShape.wordOfNat width 0 := rfl

/-- The complete original parameter survives the actual selector allocation unchanged. -/
theorem nativeRecovery_selection_push_parameter {N : Nat}
    (original : Inputs ctx N) (store : Store ctx) :
    (pushStore (modulusBits N) store).read (inputs original).parameter =
      store.read original.parameter :=
  nativeRecovery_selection_push_read original.parameter (modulusBits N) store

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Fresh scope entry and actual selection give the original early-factor flag and payload. -/
theorem nativeRecovery_selection_early_entry {N : Nat}
    (original : Inputs ctx N) (store : Store ctx) :
    let final := (earlyStep (inputs original) (refs ctx (modulusBits N))
      (pushStore (modulusBits N) store)).1
    (final.read (FirstAccepted.cellRead (accepted ctx (modulusBits N)))).toBool =
        (store.read original.parameter).second.first.toBool ∧
      final.read (FirstAccepted.cellRead (selected ctx (modulusBits N))) =
        if (store.read original.parameter).second.first.toBool then
          (store.read original.parameter).second.second
        else CShape.wordOfNat (modulusBits N) 0 := by
  have actual := nativeRecovery_early_latches (model := model) (inputs original)
    (refs ctx (modulusBits N))
    (nativeRecovery_selection_early_separated original) (pushStore (modulusBits N) store)
  have clear : ((pushStore (modulusBits N) store).read
      (FirstAccepted.cellRead (refs ctx (modulusBits N)).accepted)).toBool = false :=
    congrArg CShape.Value.toBool (nativeRecovery_selection_push_accepted (modulusBits N) store)
  have source := nativeRecovery_selection_push_parameter original store
  have sourceFlag := congrArg
    (fun value : (ParameterShape N).Value => value.second.first.toBool) source
  have sourceWord := congrArg
    (fun value : (ParameterShape N).Value => value.second.second) source
  have initialWord : (pushStore (modulusBits N) store).read
      (FirstAccepted.cellRead (refs ctx (modulusBits N)).selected) =
        CShape.wordOfNat (modulusBits N) 0 :=
    nativeRecovery_selection_push_selected (modulusBits N) store
  constructor
  · exact actual.1.trans (by rw [clear, sourceFlag]; rfl)
  · exact actual.2.trans (by
      simp only [clear, sourceFlag, sourceWord, initialWord, Bool.not_false, Bool.true_and])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout
