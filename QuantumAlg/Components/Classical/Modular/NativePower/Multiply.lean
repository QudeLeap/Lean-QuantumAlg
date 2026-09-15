/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual full-product modular multiplication

Three closed instructions multiply existing operand words, divide their exact
full-width product by an actual stored modulus, and copy the remainder into
the result width. The modulus has one additional bit, preserving the permitted
boundary modulus `2^width`. Lexical placement supplies the two scratch cells.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The division cell holds an exact wide quotient and a modulus-width remainder. -/
abbrev divisionShape (width : Nat) : CShape :=
  .product (.unsignedWord (width + width)) (.unsignedWord (width + 1))

/-- Read one actual writable cell through its structural storage reference. -/
def wordRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- The full product keeps every significant bit of the original factors. -/
def productOp (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord (width + width))) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord (width + width)) ctx ctx :=
  .mulFull width width ctx (.product left right) product

/-- Divide the actual product by the actual stored modulus. -/
def divisionOp (product : CWriteRef ctx (.unsignedWord (width + width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape width)) :
    ClassicalOp (divisionShape width) (divisionShape width) ctx ctx :=
  .divRem (width + width) (width + 1) ctx (.product (wordRead product) modulus) division

/-- Materialize the actual remainder in the caller's result cell. -/
def remainderOp (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord width) ctx ctx :=
  .wordResize (width + 1) width ctx (.second (wordRead division)) output

/-- The literal full-product, division and remainder materialization program. -/
def multiplyBody (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (productOp left right product))
    (.seq (.classical (divisionOp product modulus division))
      (.classical (remainderOp division output)))

/-- The concrete store reached by those three actual operations. -/
def multiplyStore (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  ((store.applyOp (productOp left right product)).applyOp
    (divisionOp product modulus division)).applyOp (remainderOp division output)

/-- Total finite-word expression computed by the three closed operations. -/
def multiplyValue (left right : CShape.Word width) (modulus : CShape.Word (width + 1)) :
    CShape.Word width :=
  CShape.wordResize width
    (CShape.divRem (width + width) (width + 1)
      (.product (CShape.mulFull width width (.product left right)) modulus)).second

/-- The actual three-instruction path preserves every complete quantum-reference block. -/
theorem nativePowerMultiply_execute
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (multiplyBody left right modulus product division output).execute Reference state =
      state.mapClassical (fun entry =>
        (multiplyStore left right modulus product division output entry.1,
          (entry.2, ((), ((), ()))))) := by
  simp only [multiplyBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Separated product storage yields exactly the original factors and modulus in the result. -/
theorem nativePowerMultiply_result
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (separate : product.key ∉ modulus.storageKeys) (store : Store ctx) :
    (multiplyStore left right modulus product division output store).read (wordRead output) =
      multiplyValue (store.read left) (store.read right) (store.read modulus) := by
  change (((store.applyOp (productOp left right product)).applyOp
    (divisionOp product modulus division)).applyOp (remainderOp division output)).read
      (.storage (remainderOp division output).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.wordResize width
    (((store.applyOp (productOp left right product)).applyOp
      (divisionOp product modulus division)).read
        (.storage (divisionOp product modulus division).outputRef.toCStorageRef)).second = _
  rw [Store.read_applyOp_output]
  change CShape.wordResize width
    (CShape.divRem (width + width) (width + 1) (.product
      ((store.applyOp (productOp left right product)).read (wordRead product))
      ((store.applyOp (productOp left right product)).read modulus))).second = _
  have productRead : (store.applyOp (productOp left right product)).read (wordRead product) =
      CShape.mulFull width width (.product (store.read left) (store.read right)) :=
    Store.read_applyOp_output store (productOp left right product)
  rw [productRead, Store.read_applyOp_of_not_mem_storageKeys
    store (productOp left right product) modulus separate]
  rfl

/-- The actual body changes no structural read outside its three written cells. -/
theorem nativePowerMultiply_read_other
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (productFree : product.key ∉ other.storageKeys)
    (divisionFree : division.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) (store : Store ctx) :
    (multiplyStore left right modulus product division output store).read other =
      store.read other := by
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (remainderOp division output) other outputFree).trans
      ((Store.read_applyOp_of_not_mem_storageKeys _
        (divisionOp product modulus division) other divisionFree).trans
          (Store.read_applyOp_of_not_mem_storageKeys store
            (productOp left right product) other productFree))

/-- Independent native events for one full-product modular multiplication. -/
def multiplyEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.mulFull width width),
    .classicalOperation (.divRem (width + width) (width + 1)),
    .classicalOperation (.wordResize (width + 1) width)]

/-- Exactly these three dependent operations occur in the real trace. -/
theorem nativePowerMultiply_eventTrace
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (multiplyBody left right modulus product division output).Path) :
    (multiplyBody left right modulus product division output).eventTrace path =
      multiplyEvents kind width := rfl

/-- Full-product, division and remainder materialization take three actual sequential steps. -/
theorem nativePowerMultiply_unitDepth
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + width)))
    (division : CWriteRef ctx (divisionShape width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (multiplyBody left right modulus product division output).Path) :
    (multiplyBody left right modulus product division output).depth (fun _ => 1) path = 3 := rfl

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
