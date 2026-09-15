/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store

/-!
# Actual classical references in a disjoint context union

Appending two physical contexts retains every original storage key, role,
shape and computational slot. These structural lifts introduce no read,
write, allocation or classical operation. They name the existing cells
that a subsequently compiled instruction actually reads or writes.
-/

namespace QuantumAlg.Execution.ContextUnion

private def slotLeft {kind : ProblemKind} {target : RuntimeEntry kind}
    {left : List (RuntimeEntry kind)} (right : List (RuntimeEntry kind)) :
    RuntimeEntrySlot target left → RuntimeEntrySlot target (left ++ right)
  | .here => .here
  | .there next => .there (slotLeft right next)

private def slotRight {kind : ProblemKind} {target : RuntimeEntry kind}
    (left : List (RuntimeEntry kind)) {right : List (RuntimeEntry kind)}
    (slot : RuntimeEntrySlot target right) : RuntimeEntrySlot target (left ++ right) :=
  match left with
  | [] => slot
  | _ :: tail => .there (slotRight tail slot)

variable {kind : ProblemKind} {left right : RuntimeCtx kind}
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- A left reference retains its exact entry in the actual appended context. -/
def storageLeft {shape : CShape} (ref : CStorageRef left shape) :
    CStorageRef (left.disjointUnion right separate) shape where
  key := ref.key
  role := ref.role
  slot := slotLeft right.entries ref.slot

/-- A right reference is shifted beneath the actual left entry list. -/
def storageRight {shape : CShape} (ref : CStorageRef right shape) :
    CStorageRef (left.disjointUnion right separate) shape where
  key := ref.key
  role := ref.role
  slot := slotRight left.entries ref.slot

/-- The left writable reference retains its real role and write permission. -/
def writeLeft {shape : CShape} (ref : CWriteRef left shape) :
    CWriteRef (left.disjointUnion right separate) shape where
  toCStorageRef := storageLeft separate ref.toCStorageRef
  writable := ref.writable

/-- The right writable reference retains its real role and write permission. -/
def writeRight {shape : CShape} (ref : CWriteRef right shape) :
    CWriteRef (left.disjointUnion right separate) shape where
  toCStorageRef := storageRight separate ref.toCStorageRef
  writable := ref.writable

private def mapInput {first second : RuntimeCtx kind}
    (lift : ∀ {shape}, CStorageRef first shape → CStorageRef second shape) :
    ∀ {shape}, CInputRef first shape → CInputRef second shape
  | _, .storage ref => .storage (lift ref)
  | _, .product first second => .product (mapInput lift first) (mapInput lift second)
  | _, .fixedVector entries => .fixedVector fun index => mapInput lift (entries index)
  | _, .first source => .first (mapInput lift source)
  | _, .second source => .second (mapInput lift source)
  | _, .vectorGet source index => .vectorGet (mapInput lift source) index
  | _, .bitsGet source index => .bitsGet (mapInput lift source) index
  | _, .wordBitGet source index => .wordBitGet (mapInput lift source) index

/-- Lift the complete structural left operand without computing a new value. -/
def inputLeft {shape : CShape} (input : CInputRef left shape) :
    CInputRef (left.disjointUnion right separate) shape :=
  mapInput (storageLeft separate) input

/-- Lift the complete structural right operand without computing a new value. -/
def inputRight {shape : CShape} (input : CInputRef right shape) :
    CInputRef (left.disjointUnion right separate) shape :=
  mapInput (storageRight separate) input

end QuantumAlg.Execution.ContextUnion
