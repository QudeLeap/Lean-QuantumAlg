/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Actual loaded-modulus reduction for raw field arithmetic

The original modulus workspace is allocated only upon entering reduction.
Its original MSB-first shifts and selected increments precede the original
quotient/remainder and resize instructions. Both actual lexical scopes are
released. The caller supplies no modulus word or initialized workspace.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The original loaded modulus remains in its widened actual workspace. -/
@[reducible] def loadedReductionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- Original input cells retain their identity below the actual modulus scope. -/
def underLoadedReduction {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (loadedReductionCtx ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- The real caller destination remains writable beneath the modulus allocation. -/
def writeUnderLoadedReduction {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (loadedReductionCtx ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- The freshly allocated word physically contains the loaded public modulus. -/
def loadedModulusCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (loadedReductionCtx ctx width) (.unsignedWord (width + 1)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Load the actual modulus and execute the original native reduction in sequence. -/
def loadedReductionBody (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (ConstantWord.circuit modulus spec.modulus)
    (reduceWord numerator (reductionRead modulus) output)

/-- The actual loaded-modulus and reduction records share their real intermediate store. -/
def loadedReductionBodyStep (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx ×
      (loadedReductionBody (model := model) spec numerator modulus output).Path :=
  Circuit.sequenceStoreRecord (ConstantWord.circuit (model := model) modulus spec.modulus)
    (reduceWord numerator (reductionRead modulus) output)
    (ConstantWord.foldStep modulus (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)))
    (reduceWordStep numerator (reductionRead modulus) output)

/-- Original full-state execution composes through the actual loaded modulus value. -/
theorem loadedReductionBody_execute (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadedReductionBody (model := model) spec numerator modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        ((loadedReductionBodyStep spec numerator modulus output entry.1).1,
          (entry.2.1, (entry.2.2,
            (loadedReductionBodyStep spec numerator modulus output entry.1).2)))) := by
  exact Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (ConstantWord.constantWord_fold_execute modulus _)
    (reduceWord_execute numerator (reductionRead modulus) output) Reference state

/-- All original numerator bits survive modulus loading when that internal cell is separate. -/
theorem loadedReductionBody_toNat (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (separate : modulus.key ∉ numerator.storageKeys) :
    ((loadedReductionBodyStep spec numerator modulus output store).1.read
      (reductionRead output)).toNat = (store.read numerator).toNat % spec.modulus := by
  let loaded := (ConstantWord.foldStep modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) store).1
  have modulusValue : (loaded.read (reductionRead modulus)).toNat = spec.modulus :=
    (ConstantWord.constantWord_read modulus spec.modulus store).trans
      (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec))
  have numeratorValue : loaded.read numerator = store.read numerator :=
    ConstantWord.constantWord_fold_read_other modulus _ numerator separate store
  change ((reduceWordStep numerator (reductionRead modulus) output loaded).1.read
    (reductionRead output)).toNat = _
  rw [reduceWord_original_value numerator (reductionRead modulus) output spec loaded modulusValue,
    numeratorValue]

/-- Outside its two real destinations the loaded reduction body preserves all structural reads. -/
theorem loadedReductionBody_read_other (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (modulusSeparate : modulus.key ∉ other.storageKeys)
    (outputSeparate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (loadedReductionBodyStep spec numerator modulus output store).1.read other =
      store.read other := by
  change (reduceWordStep numerator (reductionRead modulus) output _).1.read other = _
  rw [reduceWord_read_other _ _ _ other outputSeparate]
  exact ConstantWord.constantWord_fold_read_other modulus _ other modulusSeparate store

/-- Exact actual placement under the original modulus workspace. -/
def loadedReductionPlaced (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (loadedReductionCtx ctx width) (loadedReductionCtx ctx width) :=
  loadedReductionBody (model := model) spec (underLoadedReduction numerator width)
    (loadedModulusCell ctx width)
    (writeUnderLoadedReduction output width)

/-- Allocate, load and release the original modulus as part of actual raw field reduction. -/
def reduceIntoWord (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (loadedReductionPlaced spec numerator output)

/-- The certified record includes the actual modulus push and matching pop. -/
def reduceIntoWordStep (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (reduceIntoWord (model := model) spec numerator output).Path :=
  Circuit.workspaceStoreRecord ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (loadedReductionPlaced (model := model) spec numerator output)
    (loadedReductionBodyStep spec (underLoadedReduction numerator width)
      (loadedModulusCell ctx width) (writeUnderLoadedReduction output width))

/-- Real modulus preparation, division and both releases preserve the full quantum reference. -/
theorem reduceIntoWord_execute (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduceIntoWord (model := model) spec numerator output).execute Reference state =
      state.mapClassical
      (fun entry => ((reduceIntoWordStep spec numerator output entry.1).1,
        (entry.2.1, (entry.2.2, (reduceIntoWordStep spec numerator output entry.1).2)))) := by
  exact Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (loadedReductionBody_execute _ _ _ _) Reference state

omit [BitWord.Selected model] in
private theorem loadedModulusCell_avoids {shape : CShape} (input : CInputRef ctx shape) :
    (loadedModulusCell ctx width).key ∉ (underLoadedReduction input width).storageKeys := by
  change ctx.canonicalFreshKey ∉ (underLoadedReduction input width).storageKeys
  simp only [underLoadedReduction, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

/-- Every raw caller numerator is reduced modulo the original intrinsic modulus exactly. -/
theorem reduceIntoWord_toNat (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((reduceIntoWordStep spec numerator output store).1.read (reductionRead output)).toNat =
      (store.read numerator).toNat % spec.modulus := by
  unfold reduceIntoWordStep Circuit.workspaceStoreRecord
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ (reductionRead output)]
  change ((loadedReductionBodyStep _ _ _ _ _).1.read
    (reductionRead (writeUnderLoadedReduction output width))).toNat = _
  rw [loadedReductionBody_toNat _ _ _ _ _ (loadedModulusCell_avoids numerator)]
  rw [underLoadedReduction, Store.read_pushWorkspace_underWorkspace]

/-- No caller read outside the original result cell is changed by the two internal scopes. -/
theorem reduceIntoWord_read_other (spec : ModulusSpec width)
    (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (reduceIntoWordStep spec numerator output store).1.read other = store.read other := by
  unfold reduceIntoWordStep Circuit.workspaceStoreRecord
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ other]
  change (loadedReductionBodyStep _ _ _ _ _).1.read (underLoadedReduction other width) = _
  rw [loadedReductionBody_read_other _ _ _ _ _ (loadedModulusCell_avoids other)]
  · exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other
  · change output.key ∉ (underLoadedReduction other width).storageKeys
    simpa only [underLoadedReduction, CInputRef.storageKeys_underWorkspace] using separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
