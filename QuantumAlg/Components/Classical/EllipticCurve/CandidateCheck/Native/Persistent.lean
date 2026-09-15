/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained

/-!
# Original persistent recovery cells

Seven retained cells are allocated once in the original order: accepted,
selected word, inverse status, candidate word, reconstruction status, target
acceptance and scalar point. Every repeated attempt can reuse this same
context. The final two allocations are the canonical verification outputs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

private def persistentLatchCtx (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addRetained ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh

private def persistentSelectedCtx (ctx : RuntimeCtx kind) (scalarWidth : Nat) : RuntimeCtx kind :=
  (persistentLatchCtx ctx).addRetained (persistentLatchCtx ctx).canonicalFreshKey (.unsignedWord
    scalarWidth)
    (persistentLatchCtx ctx).canonicalFreshKey_fresh

private def persistentInverseCtx (ctx : RuntimeCtx kind) (scalarWidth : Nat) : RuntimeCtx kind :=
  (persistentSelectedCtx ctx scalarWidth).addRetained (persistentSelectedCtx ctx
    scalarWidth).canonicalFreshKey .bit
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh

private def persistentCandidateCtx (ctx : RuntimeCtx kind) (scalarWidth : Nat) : RuntimeCtx kind :=
  (persistentInverseCtx ctx scalarWidth).addRetained (persistentInverseCtx ctx
    scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh

private def persistentBaseCtx (ctx : RuntimeCtx kind) (scalarWidth : Nat) : RuntimeCtx kind :=
  (persistentCandidateCtx ctx scalarWidth).addRetained (persistentCandidateCtx ctx
    scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh

/-- Exactly the original seven retained cells precede the untouched caller context. -/
def persistentCtx (ctx : RuntimeCtx kind) (width scalarWidth : Nat) : RuntimeCtx kind :=
  retainedCtx (persistentBaseCtx ctx scalarWidth) width

/-- The original accepted destination remains live under all later allocations. -/
def persistentAccepted (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) .bit :=
  ((((((CWriteRef.retainedHead ctx ctx.canonicalFreshKey
    .bit ctx.canonicalFreshKey_fresh).underRetained
    (persistentLatchCtx ctx).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentLatchCtx ctx).canonicalFreshKey_fresh).underRetained
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (acceptedCtx (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey (PointShape width)
    (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey_fresh

/-- The original selected destination remains live under all later allocations. -/
def persistentSelected (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) (.unsignedWord scalarWidth) :=
  (((((CWriteRef.retainedHead (persistentLatchCtx ctx) (persistentLatchCtx ctx).canonicalFreshKey
    (.unsignedWord scalarWidth) (persistentLatchCtx ctx).canonicalFreshKey_fresh).underRetained
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (acceptedCtx (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey (PointShape width)
    (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey_fresh

/-- The original inverse-status destination remains live under all later allocations. -/
def persistentInverseSuccess (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) .bit :=
  ((((CWriteRef.retainedHead (persistentSelectedCtx ctx scalarWidth) (persistentSelectedCtx ctx
    scalarWidth).canonicalFreshKey
    .bit (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (acceptedCtx (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey (PointShape width)
    (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey_fresh

/-- The original candidate destination remains live under all later allocations. -/
def persistentCandidate (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) (.unsignedWord scalarWidth) :=
  (((CWriteRef.retainedHead (persistentInverseCtx ctx scalarWidth) (persistentInverseCtx ctx
    scalarWidth).canonicalFreshKey
    (.unsignedWord scalarWidth) (persistentInverseCtx ctx
    scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (acceptedCtx (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey (PointShape width)
    (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey_fresh

/-- The original reconstruction destination remains live under all later allocations. -/
def persistentReconstruction (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) .bit :=
  ((CWriteRef.retainedHead (persistentCandidateCtx ctx scalarWidth) (persistentCandidateCtx ctx
    scalarWidth).canonicalFreshKey
    .bit (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentBaseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (acceptedCtx (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey (PointShape width)
    (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).canonicalFreshKey_fresh

/-- The original target-acceptance destination is the canonical verification acceptance bit. -/
def persistentTargetAccepted (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) .bit :=
  retainedAccepted (persistentBaseCtx ctx scalarWidth) width

/-- The original scalar accumulator is the canonical second verification output. -/
def persistentScalar (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CWriteRef (persistentCtx ctx width scalarWidth) (PointShape width) :=
  retainedScalar (persistentBaseCtx ctx scalarWidth) width

/-- An original structural input passes through precisely the seven actual retained cells. -/
def persistentInput (width scalarWidth : Nat) {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (persistentCtx ctx width scalarWidth) shape :=
  retainedInput width ((((((input).underRetained
    ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (persistentLatchCtx ctx).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentLatchCtx ctx).canonicalFreshKey_fresh).underRetained
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
    (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).underRetained
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
    (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh)

private def retainPersistentPrefix (ctx : RuntimeCtx kind) (scalarWidth : Nat) :
    Circuit ctx (persistentBaseCtx ctx scalarWidth) :=
  .seq (.retain ctx ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh)
    (.seq (.retain (persistentLatchCtx ctx) (persistentLatchCtx ctx).canonicalFreshKey
    (.unsignedWord scalarWidth)
      (persistentLatchCtx ctx).canonicalFreshKey_fresh)
    (.seq (.retain (persistentSelectedCtx ctx scalarWidth) (persistentSelectedCtx ctx
    scalarWidth).canonicalFreshKey .bit
      (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh)
    (.seq (.retain (persistentInverseCtx ctx scalarWidth) (persistentInverseCtx ctx
    scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
      (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh)
    (.retain (persistentCandidateCtx ctx scalarWidth) (persistentCandidateCtx ctx
    scalarWidth).canonicalFreshKey .bit
      (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh))))

/-- Allocate all seven persistent cells exactly once, before the repeated attempt sequence. -/
def retainPersistent (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    Circuit ctx (persistentCtx ctx width scalarWidth) :=
  .seq (retainPersistentPrefix ctx scalarWidth)
    (retainOutputs (persistentBaseCtx ctx scalarWidth) width)

/-- The actual retained destinations in head-to-tail context order. -/
def persistentKeys (ctx : RuntimeCtx kind) (width scalarWidth : Nat) : List StorageKey :=
  [(persistentScalar ctx width scalarWidth).key,
    (persistentTargetAccepted ctx width scalarWidth).key,
    (persistentReconstruction ctx width scalarWidth).key,
    (persistentCandidate ctx width scalarWidth).key,
    (persistentInverseSuccess ctx width scalarWidth).key,
    (persistentSelected ctx width scalarWidth).key,
    (persistentAccepted ctx width scalarWidth).key]

/-- Canonical retention puts exactly these seven keys before the original context keys. -/
theorem persistentCtx_keys (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentCtx ctx width scalarWidth).keys =
      persistentKeys ctx width scalarWidth ++ ctx.keys := rfl

/-- All seven actual persistent destinations have pairwise distinct keys. -/
theorem persistentKeys_distinct (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentKeys ctx width scalarWidth).Nodup := by
  have allKeys : (persistentCtx ctx width scalarWidth).keys.Nodup :=
    (persistentCtx ctx width scalarWidth).keysNodup
  rw [persistentCtx_keys] at allKeys
  exact List.Nodup.of_append_left allKeys

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
