/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Placement
import all QuantumAlg.Components.Classical.Modular.NativePower.Arithmetic
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact multiplication through its real two-cell scope

The source-read separation of both temporary cells follows from their actual
fresh allocation. The resulting arithmetic depends only on the original
operand and modulus reads. The output may coincide with an operand cell,
permitting genuine in-place squaring without an additional persistent word.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Lifted reads name exactly their original stored keys. -/
theorem nativePower_underMultiply_storageKeys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underMultiply input width).storageKeys = input.storageKeys := by
  simp only [underMultiply, CInputRef.storageKeys_underWorkspace]

/-- The product temporary is separate from every original structural read. -/
theorem nativePower_productCell_fresh {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (productCell ctx width).key ∉ (underMultiply input width).storageKeys := by
  rw [nativePower_underMultiply_storageKeys]
  exact fun present => ctx.canonicalFreshKey_fresh
    (input.storageKeys_subset_context present)

/-- The division temporary is also separate from every original structural read. -/
theorem nativePower_divisionCell_fresh {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (divisionCell ctx width).key ∉ (underMultiply input width).storageKeys := by
  rw [underMultiply, CInputRef.storageKeys_underWorkspace]
  exact fun present => (productCtx ctx width).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

/-- Both allocations preserve the actual value of every pre-existing structural read. -/
theorem nativePower_enterMultiply_read {shape : CShape}
    (store : Store ctx) (input : CInputRef ctx shape) (width : Nat) :
    (enterMultiply store width).read (underMultiply input width) = store.read input := by
  simp only [enterMultiply, underMultiply, Store.read_pushWorkspace_underWorkspace]

/-- Popping both exact scratch heads preserves the lifted outer read. -/
theorem nativePower_leaveMultiply_read {shape : CShape}
    (store : Store (divisionCtx ctx width)) (input : CInputRef ctx shape) :
    (leaveMultiply store).read input = store.read (underMultiply input width) := by
  simp only [leaveMultiply, underMultiply, Store.read_popWorkspace_underWorkspace]

/-- Reading the lifted result is the structural lift of the original result read. -/
theorem nativePower_writeUnderMultiply_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    wordRead (writeUnderMultiply output width) = underMultiply (wordRead output) width := rfl

/-- Only the original result cell can change after the actual temporary cells are released. -/
theorem nativePower_scopedMultiply_read_other
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    ((scopedMultiplyStep left right modulus output store).1).read other =
      store.read other := by
  unfold scopedMultiplyStep
  rw [nativePower_leaveMultiply_read]
  rw [nativePowerMultiply_read_other]
  · exact nativePower_enterMultiply_read store other width
  · exact nativePower_productCell_fresh other width
  · exact nativePower_divisionCell_fresh other width
  · rw [nativePower_underMultiply_storageKeys]
    exact separate

/-- The actual scoped result is the finite-word product/reduction on the original stored values. -/
theorem nativePower_scopedMultiply_result
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((scopedMultiplyStep left right modulus output store).1).read (wordRead output) =
      multiplyValue (store.read left) (store.read right) (store.read modulus) := by
  unfold scopedMultiplyStep
  rw [nativePower_leaveMultiply_read, ← nativePower_writeUnderMultiply_read]
  rw [nativePowerMultiply_result _ _ _ _ _ _ (nativePower_productCell_fresh modulus width)]
  rw [nativePower_enterMultiply_read, nativePower_enterMultiply_read,
    nativePower_enterMultiply_read]

/-- Fitted positive actual moduli produce the exact modular product after both releases. -/
theorem nativePower_scopedMultiply_toNat
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (positive : 0 < (store.read modulus).toNat)
    (fits : (store.read modulus).toNat ≤ 2 ^ width) :
    (((scopedMultiplyStep left right modulus output store).1).read (wordRead output)).toNat =
      (store.read left).toNat * (store.read right).toNat % (store.read modulus).toNat := by
  rw [nativePower_scopedMultiply_result]
  exact nativePower_multiplyValue_toNat _ _ _ positive fits

/-- Actual lexical execution yields the concrete update and real three-operation path. -/
theorem nativePower_scopedMultiply_execute
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scopedMultiply left right modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopedMultiplyStep left right modulus output entry.1).1,
          (entry.2, (scopedMultiplyStep left right modulus output entry.1).2))) := by
  let inner := placedMultiply left right modulus output
  let innerUpdate : Store (divisionCtx ctx width) →
      Store (divisionCtx ctx width) × inner.Path := fun store =>
    (multiplyStore (underMultiply left width) (underMultiply right width)
      (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
      (writeUnderMultiply output width) store, ((), ((), ())))
  let middle := Circuit.workspace (productCtx ctx width)
    (productCtx ctx width).canonicalFreshKey (divisionShape width)
    (productCtx ctx width).canonicalFreshKey_fresh inner
  let middleUpdate : Store (productCtx ctx width) →
      Store (productCtx ctx width) × middle.Path := fun store =>
    let next := innerUpdate (store.pushWorkspace (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh)
    (Store.popWorkspace (productCtx ctx width).canonicalFreshKey (divisionShape width)
      (productCtx ctx width).canonicalFreshKey_fresh next.1, next.2)
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh middle middleUpdate
    (fun reference {_} _ initial => ?_) Reference state).trans ?_
  · refine (Circuit.execute_workspace_mapClassical (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh inner innerUpdate
      (fun reference' {_} _ initial' => ?_) reference initial).trans ?_
    · refine (nativePowerMultiply_execute _ _ _ _ _ _ reference' initial').trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · congr 1
  · congr 1

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
