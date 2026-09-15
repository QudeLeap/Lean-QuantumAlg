/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Encoding
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual fixed-word continuant materialization

One genuine Euclidean quotient updates the candidate denominator by two closed
word instructions. Their same-store result, complete quantum-reference action
and actual events are proved here. The separate lexical placement allocates
the product temporary and derives its source-read separation automatically.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Multiply the actual quotient and previous denominator in the declared finite word. -/
def continuantMultiply (quotient previous : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product quotient previous) product

/-- Add the actual older denominator to the stored low-word product. -/
def continuantAdd (product : CWriteRef ctx (.unsignedWord width))
    (older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx (.product (cellRead product) older) candidate

/-- The literal two-operation continuant program. -/
def continuantBody (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (continuantMultiply quotient previous product))
    (.classical (continuantAdd product older candidate))

/-- The concrete store reached by those two actual closed operations. -/
def continuantStore (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (store.applyOp (continuantMultiply quotient previous product)).applyOp
    (continuantAdd product older candidate)

/-- The independent fixed-word recurrence includes its exact wrapping arithmetic. -/
def continuantValue (quotient previous older : CShape.Value (.unsignedWord width)) :
    CShape.Value (.unsignedWord width) :=
  Resource.WordBinaryOpcode.eval .add width
    (.product (Resource.WordBinaryOpcode.eval .mulLow width (.product quotient previous)) older)

/-- The actual execution updates the same store and retains every complete reference block. -/
theorem nativeContinuant_execute
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (continuantBody quotient previous older product candidate).execute Reference state =
      state.mapClassical (fun entry =>
        (continuantStore quotient previous older product candidate entry.1,
          (entry.2, ((), ())))) := by
  simp only [continuantBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- A separated product temporary yields the exact recurrence on the original operand reads. -/
theorem nativeContinuant_result
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width))
    (separate : product.key ∉ older.storageKeys) (store : Store ctx) :
    (continuantStore quotient previous older product candidate store).read (cellRead candidate) =
      continuantValue (store.read quotient) (store.read previous) (store.read older) := by
  change ((store.applyOp (continuantMultiply quotient previous product)).applyOp
    (continuantAdd product older candidate)).read
      (.storage (continuantAdd product older candidate).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change Resource.WordBinaryOpcode.eval .add width (.product
    ((store.applyOp (continuantMultiply quotient previous product)).read (cellRead product))
    ((store.applyOp (continuantMultiply quotient previous product)).read older)) = _
  have productRead : (store.applyOp (continuantMultiply quotient previous product)).read
      (cellRead product) = Resource.WordBinaryOpcode.eval .mulLow width
        (.product (store.read quotient) (store.read previous)) :=
    Store.read_applyOp_output store (continuantMultiply quotient previous product)
  rw [productRead, Store.read_applyOp_of_not_mem_storageKeys
    store (continuantMultiply quotient previous product) older separate]
  rfl

/-- Every actual read outside the two written cells is preserved by the complete body. -/
theorem nativeContinuant_read_other
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (productSeparate : product.key ∉ other.storageKeys)
    (candidateSeparate : candidate.key ∉ other.storageKeys) (store : Store ctx) :
    (continuantStore quotient previous older product candidate store).read other =
      store.read other := by
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (continuantAdd product older candidate) other candidateSeparate).trans
      (Store.read_applyOp_of_not_mem_storageKeys store
        (continuantMultiply quotient previous product) other productSeparate)

/-- Independent native events of one materialized finite continuant. -/
def continuantEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .add width)]

/-- Exactly the actual multiply and add occur on every body path. -/
theorem nativeContinuant_eventTrace
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width))
    (path : (continuantBody quotient previous older product candidate).Path) :
    (continuantBody quotient previous older product candidate).eventTrace path =
      continuantEvents kind width := rfl

/-- These two dependent operations have exactly two units of actual depth. -/
theorem nativeContinuant_unitDepth
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (product candidate : CWriteRef ctx (.unsignedWord width))
    (path : (continuantBody quotient previous older product candidate).Path) :
    (continuantBody quotient previous older product candidate).depth (fun _ => 1) path = 2 := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
