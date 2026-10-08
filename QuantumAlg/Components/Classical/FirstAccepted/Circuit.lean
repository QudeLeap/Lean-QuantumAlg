/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Store
public import QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Native first-accepted selection

The selector computes availability and eligibility using two actual Boolean
instructions. Its stored take bit selects either two copies or identity.
The existing persistent latches and scratch cells are intrinsically writable;
the circuit allocates no new storage and records the selected branch itself.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

noncomputable section

open Execution

/-- The candidate and its already computed acceptance predicate. -/
public structure Inputs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Stored predicate deciding whether this candidate is eligible. -/
  eligible : CInputRef ctx .bit
  /-- Existing candidate word, including the unique width-zero word. -/
  candidate : CInputRef ctx (.unsignedWord width)

/-- Persistent output latches and the actual two Boolean scratch cells. -/
public structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
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
public def cellRead {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Compute the actual negated persistent latch. -/
public def availableOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (cellRead refs.accepted) refs.available

/-- Conjoin actual availability with the stored eligibility predicate. -/
public def takeOp (inputs : Inputs ctx width) (refs : Refs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (cellRead refs.available) inputs.eligible) refs.take

/-- Copy the candidate to the persistent selected-word cell. -/
public def selectedCopyOp (inputs : Inputs ctx width) (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx inputs.candidate refs.selected

/-- Copy the actual take bit to the persistent acceptance latch. -/
public def acceptedCopyOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .copy ctx (cellRead refs.take) refs.accepted

/-- The selected arm contains exactly the word copy and the latch copy. -/
public def copyBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit
      model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (selectedCopyOp inputs refs))
    (BitWord.instruction (execution := model) (acceptedCopyOp refs))

/-- The two unconditional Boolean instructions compute the branch's stored predicate. -/
public def decisionBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit
      model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (availableOp refs)) (BitWord.instruction
    (execution := model) (takeOp inputs refs))

/-- Select the actual copy arm from the value read at the take reference. -/
public def conditionalCopy {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit
      model ctx ctx :=
  .branch (cellRead refs.take) (fun value =>
    if value.toBool then copyBody (model := model) inputs refs else .id ctx)

/-- One complete native selector step, with no storage allocation. -/
public def circuit {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width) : Circuit
      model ctx ctx :=
  .seq (decisionBody (model := model) inputs refs) (conditionalCopy (model := model) inputs refs)

/-- The real unconditional native outputs follow the two sequential scratch writes. -/
public def decisionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width)
    (before : Store ctx) : Store ctx × (decisionBody (model := model) inputs refs).Path :=
  let available := BitWord.instructionStep (execution := model) (availableOp refs) before
  let taken := BitWord.instructionStep (execution := model) (takeOp inputs refs) available.1
  (taken.1, (available.2, taken.2))

/-- The actual selected copy outputs retain chronological writes, including source aliases. -/
public def copyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (refs : Refs ctx width)
    (before : Store ctx) : Store ctx × (copyBody (model := model) inputs refs).Path :=
  let selected := BitWord.instructionStep (execution := model) (selectedCopyOp inputs refs) before
  let accepted := BitWord.instructionStep (execution := model) (acceptedCopyOp refs) selected.1
  (accepted.1, (selected.2, accepted.2))

/-- The actual pair of Boolean writes before the branch. -/
public def decisionStore (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  (store.applyOp (availableOp refs)).applyOp (takeOp inputs refs)

/-- The actual pair of writes in the selected copy arm. -/
public def copyStore (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  (store.applyOp (selectedCopyOp inputs refs)).applyOp (acceptedCopyOp refs)

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
