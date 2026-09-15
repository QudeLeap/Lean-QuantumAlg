/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Store

/-!
# Native first-accepted selection

The selector computes availability and eligibility using two actual Boolean
instructions. Its stored take bit selects either two copies or identity.
The existing persistent latches and scratch cells are intrinsically writable;
the circuit allocates no new storage and records the selected branch itself.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

/-- The candidate and its already computed acceptance predicate. -/
structure Inputs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Stored predicate deciding whether this candidate is eligible. -/
  eligible : CInputRef ctx .bit
  /-- Existing candidate word, including the unique width-zero word. -/
  candidate : CInputRef ctx (.unsignedWord width)

/-- Persistent output latches and the actual two Boolean scratch cells. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Whether a previous candidate has been accepted. -/
  accepted : CWriteRef ctx .bit
  /-- The word stored by the first accepted candidate. -/
  selected : CWriteRef ctx (.unsignedWord width)
  /-- Scratch value of the negated acceptance latch. -/
  available : CWriteRef ctx .bit
  /-- Scratch predicate that controls the real copy branch. -/
  take : CWriteRef ctx .bit

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Read the same cell to which a closed classical instruction may write. -/
def cellRead {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Compute the actual negated persistent latch. -/
def availableOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (cellRead refs.accepted) refs.available

/-- Conjoin actual availability with the stored eligibility predicate. -/
def takeOp (inputs : Inputs ctx width) (refs : Refs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (cellRead refs.available) inputs.eligible) refs.take

/-- Copy the candidate to the persistent selected-word cell. -/
def selectedCopyOp (inputs : Inputs ctx width) (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx inputs.candidate refs.selected

/-- Copy the actual take bit to the persistent acceptance latch. -/
def acceptedCopyOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .copy ctx (cellRead refs.take) refs.accepted

/-- The selected arm contains exactly the word copy and the latch copy. -/
def copyBody (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (selectedCopyOp inputs refs)) (.classical (acceptedCopyOp refs))

/-- The two unconditional Boolean instructions compute the branch's stored predicate. -/
def decisionBody (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (availableOp refs)) (.classical (takeOp inputs refs))

/-- Select the actual copy arm from the value read at the take reference. -/
def conditionalCopy (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (cellRead refs.take) (fun value =>
    if value.toBool then copyBody inputs refs else .id ctx)

/-- One complete native selector step, with no storage allocation. -/
def circuit (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (decisionBody inputs refs) (conditionalCopy inputs refs)

/-- The actual pair of Boolean writes before the branch. -/
def decisionStore (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  (store.applyOp (availableOp refs)).applyOp (takeOp inputs refs)

/-- The actual pair of writes in the selected copy arm. -/
def copyStore (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  (store.applyOp (selectedCopyOp inputs refs)).applyOp (acceptedCopyOp refs)

end QuantumAlg.ClassicalRoutines.FirstAccepted
