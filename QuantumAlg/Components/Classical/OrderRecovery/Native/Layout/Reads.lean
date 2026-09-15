/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout

/-!
# Exact readback through the finite recovery scopes

Structural lifts preserve actual original reads, and each field reads the
canonical initial value of its own real workspace head. The field-list proofs
cover all named recovery cells once, rather than postulating initialization
or supplying independent observations to the recovery program.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}

/-- An original structural read has exactly the same support under all recovery fields. -/
theorem nativeRecovery_underFields_keys (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (input : CInputRef ctx shape) :
    (underRecoveryFields modulusWidth candidateWidth fields input).storageKeys =
      input.storageKeys := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      change (underRecoveryFields modulusWidth candidateWidth rest
        (input.underWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field)
          ctx.canonicalFreshKey_fresh)).storageKeys = _
      rw [ih, CInputRef.storageKeys_underWorkspace]

/-- Lifting an actual destination never changes its real key. -/
theorem nativeRecovery_writeUnderFields_key (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (output : CWriteRef ctx shape) :
    (writeUnderRecoveryFields modulusWidth candidateWidth fields output).key = output.key := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      exact ih (output.underWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Reading a lifted destination is the actual lift of its original storage read. -/
theorem nativeRecovery_read_writeUnderFields (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (output : CWriteRef ctx shape) :
    cellRead (writeUnderRecoveryFields modulusWidth candidateWidth fields output) =
      underRecoveryFields modulusWidth candidateWidth fields (cellRead output) := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      exact ih (output.underWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Allocating the real field list preserves every original structural read. -/
theorem nativeRecovery_enter_read (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (store : Store ctx) (input : CInputRef ctx shape) :
    (enterRecoveryFields modulusWidth candidateWidth fields store).read
      (underRecoveryFields modulusWidth candidateWidth fields input) = store.read input := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      change (enterRecoveryFields modulusWidth candidateWidth rest
        (store.pushWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field)
          ctx.canonicalFreshKey_fresh)).read
        (underRecoveryFields modulusWidth candidateWidth rest
          (input.underWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field)
            ctx.canonicalFreshKey_fresh)) = _
      rw [ih, Store.read_pushWorkspace_underWorkspace]

/-- Releasing the real field list exposes the same original structural reads. -/
theorem nativeRecovery_leave_read (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField)
    (store : Store (fieldsContext ctx modulusWidth candidateWidth fields))
    (input : CInputRef ctx shape) :
    (leaveRecoveryFields ctx modulusWidth candidateWidth fields store).read input =
      store.read (underRecoveryFields modulusWidth candidateWidth fields input) := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      change (Store.popWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh
        (leaveRecoveryFields _ modulusWidth candidateWidth rest store)).read input = _
      rw [Store.read_popWorkspace_underWorkspace, ih]
      rfl

/-- Every actual field reads the canonical initial encoding of its genuine fresh head. -/
theorem nativeRecovery_enter_field (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (index : Fin fields.length) (store : Store ctx) :
    (enterRecoveryFields modulusWidth candidateWidth fields store).read
        (cellRead (recoveryFieldCell ctx modulusWidth candidateWidth fields index)) =
      CShape.initialValue (recoveryFieldShape modulusWidth candidateWidth (fields.get index)) := by
  induction fields generalizing ctx with
  | nil => exact Fin.elim0 index
  | cons field rest ih =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · change (enterRecoveryFields modulusWidth candidateWidth rest
          (store.pushWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field)
            ctx.canonicalFreshKey_fresh)).read
          (cellRead (writeUnderRecoveryFields modulusWidth candidateWidth rest
            (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
              (recoveryFieldShape modulusWidth candidateWidth field)
              ctx.canonicalFreshKey_fresh))) =
          CShape.initialValue (recoveryFieldShape modulusWidth candidateWidth field)
        rw [nativeRecovery_read_writeUnderFields, nativeRecovery_enter_read]
        rfl
      · exact ih tail (store.pushWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- No recovery field allocation adds or removes a quantum physical wire. -/
theorem nativeRecovery_fields_quantumWires (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) :
    (fieldsContext ctx modulusWidth candidateWidth fields).quantumWires = ctx.quantumWires := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      exact ih (ctx := ctx.addWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
