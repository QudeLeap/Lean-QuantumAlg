/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction
import all QuantumAlg.Components.Classical.Modular.NativePower.Arithmetic
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Actual original full-product field multiplication

The original full product is written before allocating and loading the real
modulus. Native quotient/remainder and resize instructions then reduce that
product. All three actual scopes are released; arbitrary caller operands,
output aliases, quantum references and execution histories are retained.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual product storage precedes both original reduction workspaces. -/
@[reducible] def multiplicationCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- Original inputs retain their actual identity under full-product storage. -/
def underMultiplication {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (multiplicationCtx ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- The caller result remains writable under the original product allocation. -/
def writeUnderMultiplication {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (multiplicationCtx ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- The exact combined-width product lives in this actual fresh word. -/
def multiplicationProduct (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (multiplicationCtx ctx width) (.unsignedWord (width + width)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- Compute the full product, then allocate and load the original reduction modulus. -/
def multiplicationBody (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (Modular.NativePower.productOp left right product))
    (reduceIntoWord spec (reductionRead product) output)

/-- The actual record carries the product write into the subsequent loaded reduction. -/
def multiplicationBodyStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (multiplicationBody spec left right product output).Path :=
  Circuit.sequenceRecord (.classical (Modular.NativePower.productOp left right product))
    (reduceIntoWord spec (reductionRead product) output)
    (fun store => (store.applyOp (Modular.NativePower.productOp left right product), ()))
    (reduceIntoWordStep spec (reductionRead product) output)

/-- Both actual stages preserve every complete quantum-reference block and original history. -/
theorem multiplicationBody_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (multiplicationBody spec left right product output).execute Reference state =
      state.mapClassical (fun entry =>
        ((multiplicationBodyStep spec left right product output entry.1).1,
          (entry.2, (multiplicationBodyStep spec left right product output entry.1).2))) := by
  apply Circuit.execute_sequenceRecord _ _ _ _ ?_ (reduceIntoWord_execute _ _ _) Reference state
  intro Ref H finite initial
  refine (Circuit.execute_classical_mapClassical _ Ref initial).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The exact combined-width product gives modular multiplication for every raw operand. -/
theorem multiplicationBody_toNat (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((multiplicationBodyStep spec left right product output store).1.read
      (reductionRead output)).toNat =
        (store.read left).toNat * (store.read right).toNat % spec.modulus := by
  change ((reduceIntoWordStep spec (reductionRead product) output
    (store.applyOp (Modular.NativePower.productOp left right product))).1.read
      (reductionRead output)).toNat = _
  rw [reduceIntoWord_toNat]
  have written : (store.applyOp (Modular.NativePower.productOp left right product)).read
      (reductionRead product) =
        CShape.mulFull width width (.product (store.read left) (store.read right)) :=
    Store.read_applyOp_output store (Modular.NativePower.productOp left right product)
  rw [written, Modular.NativePower.nativePower_fullProduct_exact]

/-- The original body preserves every structural read outside product and caller result. -/
theorem multiplicationBody_read_other (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (productFree : product.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) (store : Store ctx) :
    (multiplicationBodyStep spec left right product output store).1.read other =
      store.read other := by
  change (reduceIntoWordStep spec (reductionRead product) output _).1.read other = _
  rw [reduceIntoWord_read_other _ _ _ other outputFree]
  exact Store.read_applyOp_of_not_mem_storageKeys store
    (Modular.NativePower.productOp left right product) other productFree

/-- The actual full-product body uses transported caller inputs and output. -/
def multiplicationPlaced (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (multiplicationCtx ctx width) (multiplicationCtx ctx width) :=
  multiplicationBody spec (underMultiplication left width) (underMultiplication right width)
    (multiplicationProduct ctx width) (writeUnderMultiplication output width)

/-- Allocate the original product, run the original loaded reduction, and release all scratch. -/
def mulIntoWord (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh (multiplicationPlaced spec left right output)

/-- The record includes the real product push, every native operation, and matching pop. -/
def mulIntoWordStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (mulIntoWord spec left right output).Path :=
  Circuit.workspaceRecord ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh (multiplicationPlaced spec left right output)
    (multiplicationBodyStep spec (underMultiplication left width)
      (underMultiplication right width) (multiplicationProduct ctx width)
      (writeUnderMultiplication output width))

/-- The actual product and loaded reduction preserve the complete reference and actual history. -/
theorem mulIntoWord_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (mulIntoWord spec left right output).execute Reference state = state.mapClassical
      (fun entry => ((mulIntoWordStep spec left right output entry.1).1,
        (entry.2, (mulIntoWordStep spec left right output entry.1).2))) := by
  exact Circuit.execute_workspaceRecord _ _ _ _ _ (multiplicationBody_execute _ _ _ _ _)
    Reference state

/-- Actual loaded field multiplication computes the canonical product on every raw input. -/
theorem mulIntoWord_toNat (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((mulIntoWordStep spec left right output store).1.read (reductionRead output)).toNat =
      (store.read left).toNat * (store.read right).toNat % spec.modulus := by
  unfold mulIntoWordStep Circuit.workspaceRecord
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ (reductionRead output)]
  change ((multiplicationBodyStep _ _ _ _ _ _).1.read
    (reductionRead (writeUnderMultiplication output width))).toNat = _
  rw [multiplicationBody_toNat]
  simp only [underMultiplication, Store.read_pushWorkspace_underWorkspace]

/-- Actual fresh product storage cannot alter any original caller input. -/
private theorem multiplicationProduct_avoids {shape : CShape} (input : CInputRef ctx shape) :
    (multiplicationProduct ctx width).key ∉ (underMultiplication input width).storageKeys := by
  change ctx.canonicalFreshKey ∉ (underMultiplication input width).storageKeys
  simp only [underMultiplication, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

/-- Every structural caller read outside the result survives all actual internal scopes. -/
theorem mulIntoWord_read_other (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (mulIntoWordStep spec left right output store).1.read other = store.read other := by
  unfold mulIntoWordStep Circuit.workspaceRecord
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ other]
  change (multiplicationBodyStep _ _ _ _ _ _).1.read (underMultiplication other width) = _
  rw [multiplicationBody_read_other _ _ _ _ _ _ (multiplicationProduct_avoids other)]
  · exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other
  · change output.key ∉ (underMultiplication other width).storageKeys
    simpa only [underMultiplication, CInputRef.storageKeys_underWorkspace] using separate

/-- No caller cell except the actual output changes, even when that output aliases an operand. -/
theorem mulIntoWordStep_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (mulIntoWordStep spec left right output store).1 = store.write output
      (CShape.wordOfNat width
        ((store.read left).toNat * (store.read right).toNat % spec.modulus)) := by
  apply Store.store_eq_write_of_read_frame
  · have actual := mulIntoWord_toNat spec left right output store
    have fitted : (store.read left).toNat * (store.read right).toNat % spec.modulus <
        2 ^ width := lt_of_lt_of_le (Nat.mod_lt _ (modulusSpec_modulus_pos spec)) spec.le_capacity
    cases value : (mulIntoWordStep spec left right output store).1.read
      (.storage output.toCStorageRef) with
    | unsignedWord result =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      change result.val = _ % 2 ^ width
      rw [Nat.mod_eq_of_lt fitted]
      change ((mulIntoWordStep spec left right output store).1.read
        (.storage output.toCStorageRef)).toNat = _ at actual
      rw [value] at actual
      exact actual
  · intro shape input separate
    exact mulIntoWord_read_other spec left right output (.storage input)
      (by simpa [CInputRef.storageKeys] using separate) store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
