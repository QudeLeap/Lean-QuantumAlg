/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Word
public import QuantumAlg.Core.Execution.Retained.Step
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Core.Execution.Retained.Step
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.Arithmetic

/-! Native retained-result MulFull circuit and its exact arithmetic bridge. -/

namespace QuantumAlg.ClassicalRoutines.MulFull

/-- Closed operand shape for independently sized multiplication. -/
public abbrev InputShape (leftWidth rightWidth : Nat) : CShape :=
  .product (.unsignedWord leftWidth) (.unsignedWord rightWidth)

/-- Closed full-width product shape. -/
public abbrev OutputShape (leftWidth rightWidth : Nat) : CShape :=
  .unsignedWord (leftWidth + rightWidth)

/-- Encode the pure multiplication operands for the typed machine. -/
def encodeInput {leftWidth rightWidth : Nat}
    (input : ClassicalAlgorithms.MulFull.Input
      leftWidth rightWidth) :
    CShape.Value (InputShape leftWidth rightWidth) :=
  .product (encodeWord input.left) (encodeWord input.right)

/-- Decode typed-machine multiplication operands to the pure carrier. -/
def decodeInput {leftWidth rightWidth : Nat}
    (input : CShape.Value (InputShape leftWidth rightWidth)) :
    ClassicalAlgorithms.MulFull.Input leftWidth rightWidth where
  left := decodeWord input.first
  right := decodeWord input.second

/-- Encode the pure full-width product for the typed machine. -/
def encodeOutput {leftWidth rightWidth : Nat}
    (output : ClassicalAlgorithms.MulFull.Output
      leftWidth rightWidth) :
    CShape.Value (OutputShape leftWidth rightWidth) :=
  encodeWord output.value

/-- Decode the typed-machine full-width product. -/
def decodeOutput {leftWidth rightWidth : Nat}
    (output : CShape.Value (OutputShape leftWidth rightWidth)) :
    ClassicalAlgorithms.MulFull.Output leftWidth rightWidth where
  value := decodeWord output

@[simp] theorem fixedWidthMulFull_decode_encode_input
    {leftWidth rightWidth : Nat}
    (input : ClassicalAlgorithms.MulFull.Input
      leftWidth rightWidth) :
    decodeInput (encodeInput input) = input := by
  cases input
  rfl

@[simp] theorem fixedWidthMulFull_encode_decode_input
    {leftWidth rightWidth : Nat}
    (input : CShape.Value (InputShape leftWidth rightWidth)) :
    encodeInput (decodeInput input) = input := by
  cases input with
  | product left right =>
      cases left
      cases right
      rfl

@[simp] theorem fixedWidthMulFull_decode_encode_output
    {leftWidth rightWidth : Nat}
    (output : ClassicalAlgorithms.MulFull.Output
      leftWidth rightWidth) :
    decodeOutput (encodeOutput output) = output := by
  cases output
  rfl

@[simp] theorem fixedWidthMulFull_encode_decode_output
    {leftWidth rightWidth : Nat}
    (output : CShape.Value (OutputShape leftWidth rightWidth)) :
    encodeOutput (decodeOutput output) = output := by
  cases output
  rfl

/-- The Core full-product instruction and the pure evaluator agree completely. -/
theorem fixedWidthMulFull_core_eval_bridge {leftWidth rightWidth : Nat}
    (input : CShape.Value (InputShape leftWidth rightWidth)) :
    decodeOutput (CShape.mulFull leftWidth rightWidth input) =
      ClassicalAlgorithms.MulFull.eval (decodeInput input) := by
  cases input with
  | product left right =>
      cases left
      cases right
      rfl

/-- The retained cell read by the caller after the actual arithmetic instruction. -/
def resultRef {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (resultKey : StorageKey) (leftWidth rightWidth : Nat) (fresh : resultKey ∉ ctx.keys) :
    CInputRef (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh) (OutputShape
      leftWidth rightWidth) :=
  .storage (CStorageRef.retainedHead ctx resultKey (OutputShape leftWidth rightWidth) fresh)

/-- One closed instruction reads the supplied operands and writes the fresh result cell. -/
def instruction {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    ClassicalOp (InputShape leftWidth rightWidth) (OutputShape leftWidth rightWidth)
      (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh) (ctx.addRetained
        resultKey (OutputShape leftWidth rightWidth) fresh) :=
  .mulFull leftWidth rightWidth (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh)
    (input.underRetained resultKey (OutputShape leftWidth rightWidth) fresh)
    (CWriteRef.retainedHead ctx resultKey (OutputShape leftWidth rightWidth) fresh)

/-- The composable native circuit allocates its result and executes the arithmetic operation. -/
def routine {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    Circuit ctx (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh) :=
  Circuit.retainedStep ctx resultKey (OutputShape leftWidth rightWidth) fresh
    (instruction ctx leftWidth rightWidth input resultKey fresh)

/-- The actual store update appearing in the circuit execution equation. -/
def finalStore {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) : Execution.Store (ctx.addRetained resultKey (OutputShape
      leftWidth rightWidth) fresh) :=
  (store.pushRetained resultKey (OutputShape leftWidth rightWidth) fresh).applyOp
    (instruction ctx leftWidth rightWidth input resultKey fresh)

/-- Reading the written cell gives the native arithmetic evaluator on the original operands. -/
theorem finalStore_read {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) :
    (finalStore ctx leftWidth rightWidth input resultKey fresh store).read (resultRef ctx
      resultKey leftWidth rightWidth fresh) =
      CShape.mulFull leftWidth rightWidth (store.read input) := by
  change ((store.pushRetained resultKey (OutputShape leftWidth rightWidth) fresh).applyOp
    (instruction ctx leftWidth rightWidth input resultKey fresh)).read
      (.storage (instruction ctx leftWidth rightWidth input resultKey
        fresh).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.mulFull leftWidth rightWidth
    ((store.pushRetained resultKey (OutputShape leftWidth rightWidth) fresh).read
      (input.underRetained resultKey (OutputShape leftWidth rightWidth) fresh)) = _
  rw [Execution.Store.read_pushRetained_underRetained]

/-- The result of the actual store update agrees with the pure arithmetic specification. -/
theorem fixedWidthMulFull_eval_bridge {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) :
    decodeOutput ((finalStore ctx leftWidth rightWidth input resultKey fresh store).read
      (resultRef ctx resultKey leftWidth rightWidth fresh)) =
        ClassicalAlgorithms.MulFull.eval (decodeInput (store.read input)) := by
  rw [finalStore_read]
  exact fixedWidthMulFull_core_eval_bridge (store.read input)

/-- Actual paths emit exactly the one native classical arithmetic event. -/
theorem fixedWidthMulFull_eventTrace_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx leftWidth rightWidth input resultKey fresh).Path) :
    (routine ctx leftWidth rightWidth input resultKey fresh).eventTrace path =
      [(.classicalOperation (.mulFull leftWidth rightWidth) : Resource.Event kind)] := rfl

/-- The actual native event multiplicity has no separately supplied cost witness. -/
theorem fixedWidthMulFull_resourcePool_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx leftWidth rightWidth input resultKey fresh).Path) :
    (routine ctx leftWidth rightWidth input resultKey fresh).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.mulFull leftWidth rightWidth)) := by
  change ResourcePool.ofList [(.classicalOperation (.mulFull leftWidth rightWidth) :
    Resource.Event kind)] = _
  simp

/-- The complete extended context determines the actual resident peak. -/
theorem fixedWidthMulFull_peakResidentSpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx leftWidth rightWidth input resultKey fresh).Path) :
    (routine ctx leftWidth rightWidth input resultKey fresh).peakResidentSpace path =
      (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh).residentSpace :=
  Circuit.retainedStep_peakResidentSpace ctx resultKey (OutputShape leftWidth rightWidth) fresh
    (instruction ctx leftWidth rightWidth input resultKey fresh) path

/-- The retained result is included in the actual auxiliary peak. -/
theorem fixedWidthMulFull_peakAuxiliarySpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx leftWidth rightWidth input resultKey fresh).Path) :
    (routine ctx leftWidth rightWidth input resultKey fresh).peakAuxiliarySpace path =
      (ctx.addRetained resultKey (OutputShape leftWidth rightWidth) fresh).auxiliarySpace :=
  Circuit.retainedStep_peakAuxiliarySpace ctx resultKey (OutputShape leftWidth rightWidth) fresh
    (instruction ctx leftWidth rightWidth input resultKey fresh) path

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The common interpreter performs this update on complete states with any external reference. -/
theorem fixedWidthMulFull_execute {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx leftWidth rightWidth input resultKey fresh).execute Reference state =
      state.mapClassical (fun value =>
        (finalStore ctx leftWidth rightWidth input resultKey fresh value.1, (value.2, ((), ())))) :=
  Circuit.execute_retainedStep ctx resultKey (OutputShape leftWidth rightWidth) fresh
    (instruction ctx leftWidth rightWidth input resultKey fresh) state

/-- Borrowed values and their full external quantum correlations survive the actual circuit. -/
theorem fixedWidthMulFull_borrowedRestored {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (leftWidth rightWidth : Nat)
    (input : CInputRef ctx (InputShape leftWidth rightWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx leftWidth rightWidth input resultKey fresh).BorrowedRestored Reference state
      ((routine ctx leftWidth rightWidth input resultKey fresh).execute Reference state) :=
  Circuit.retainedStep_borrowedRestored ctx resultKey (OutputShape leftWidth rightWidth) fresh
    (instruction ctx leftWidth rightWidth input resultKey fresh) state

end

end QuantumAlg.ClassicalRoutines.MulFull
