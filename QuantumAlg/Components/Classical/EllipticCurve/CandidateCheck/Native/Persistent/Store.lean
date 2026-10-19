/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained.Semantics

/-!
# Canonical persistent allocation store

The seven actual retain initializations, original structural reads, exact
storage keys and initial values, without a caller layout or initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The actual seven initializations, with the canonical verification pair last. -/
def persistentInitialStore (width scalarWidth : Nat) (before : Store ctx) :
    Store (persistentCtx ctx width scalarWidth) :=
  retainedInitialStore width ((((((before).pushRetained
    ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).pushRetained
    (persistentLatchCtx ctx).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentLatchCtx ctx).canonicalFreshKey_fresh).pushRetained
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).pushRetained
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).pushRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh)

/-- The actual allocation record includes all seven literal retain paths. -/
def persistentAllocationStep {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (width scalarWidth : Nat) (before : Store ctx) :
    Store (persistentCtx ctx width scalarWidth) × (retainPersistent ctx width scalarWidth).Path :=
  (persistentInitialStore width scalarWidth before, (((), ((), ((), ((), ())))), ((), ())))

/-- Every original structural input keeps its exact value after the seven actual allocations. -/
lemma persistentInitialStore_read (width scalarWidth : Nat) (before : Store ctx)
    {shape : CShape} (input : CInputRef ctx shape) :
    (persistentInitialStore width scalarWidth before).read
      (persistentInput width scalarWidth input) = before.read input := by
  dsimp only [persistentInitialStore, persistentInput]
  erw [retainedInitialStore_read]
  erw [Store.read_pushRetained_underRetained, Store.read_pushRetained_underRetained,
    Store.read_pushRetained_underRetained, Store.read_pushRetained_underRetained,
    Store.read_pushRetained_underRetained]

/-- The seven structural lifts keep precisely the original input storage keys. -/
lemma persistentInput_storageKeys (width scalarWidth : Nat)
    {shape : CShape} (input : CInputRef ctx shape) :
    (persistentInput width scalarWidth input).storageKeys = input.storageKeys := by
  dsimp only [persistentInput, retainedInput]
  erw [CInputRef.storageKeys_underRetained, CInputRef.storageKeys_underRetained,
    CInputRef.storageKeys_underRetained, CInputRef.storageKeys_underRetained,
    CInputRef.storageKeys_underRetained, CInputRef.storageKeys_underRetained,
    CInputRef.storageKeys_underRetained]

/-- Actual context key uniqueness separates every persistent destination from the original input. -/
lemma persistentInput_separate (width scalarWidth : Nat)
    {shape : CShape} (input : CInputRef ctx shape) (key : StorageKey)
    (persistent : key ∈ persistentKeys ctx width scalarWidth) :
    key ∉ (persistentInput width scalarWidth input).storageKeys := by
  have allKeys : (persistentCtx ctx width scalarWidth).keys.Nodup :=
    (persistentCtx ctx width scalarWidth).keysNodup
  rw [persistentCtx_keys] at allKeys
  have disjoint := List.disjoint_of_nodup_append allKeys
  rw [List.disjoint_left] at disjoint
  rw [persistentInput_storageKeys]
  exact fun present => disjoint persistent (CInputRef.storageKeys_subset_context input present)

/-- Actual allocation gives the original accepted cell its shape's initial encoding. -/
lemma persistentInitialStore_accepted (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentAccepted ctx width scalarWidth)) =
        CShape.initialValue .bit := rfl

/-- Actual allocation gives the original selected cell its shape's initial encoding. -/
lemma persistentInitialStore_selected (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentSelected ctx width scalarWidth)) =
        CShape.initialValue (.unsignedWord scalarWidth) := rfl

/-- Actual allocation gives the original inverse-status cell its shape's initial encoding. -/
lemma persistentInitialStore_inverseSuccess (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentInverseSuccess ctx width scalarWidth)) =
        CShape.initialValue .bit := rfl

/-- Actual allocation gives the original candidate cell its shape's initial encoding. -/
lemma persistentInitialStore_candidate (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentCandidate ctx width scalarWidth)) =
        CShape.initialValue (.unsignedWord scalarWidth) := rfl

/-- Actual allocation gives the original reconstruction cell its shape's initial encoding. -/
lemma persistentInitialStore_reconstruction (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentReconstruction ctx width scalarWidth)) =
        CShape.initialValue .bit := rfl

/-- Actual allocation gives the original target-acceptance cell its shape's initial encoding. -/
lemma persistentInitialStore_targetAccepted (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentTargetAccepted ctx width scalarWidth)) =
        CShape.initialValue .bit := rfl

/-- Actual allocation gives the original scalar cell its shape's initial encoding. -/
lemma persistentInitialStore_scalar (width scalarWidth : Nat) (before : Store ctx) :
    (persistentInitialStore width scalarWidth before).read
      (Add.Native.classifierRead (persistentScalar ctx width scalarWidth)) =
        CShape.initialValue (PointShape width) := rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
