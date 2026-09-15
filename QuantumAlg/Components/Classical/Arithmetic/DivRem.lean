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

/-! Native retained-result DivRem circuit and its exact arithmetic bridge. -/

namespace QuantumAlg.ClassicalRoutines.DivRem

/-- Closed operand shape for numerator and divisor words. -/
public abbrev InputShape (numeratorWidth divisorWidth : Nat) : CShape :=
  .product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)

/-- Closed result shape for quotient and remainder words. -/
public abbrev OutputShape (numeratorWidth divisorWidth : Nat) : CShape :=
  .product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)

/-- Encode the pure division operands for the typed machine. -/
def encodeInput {numeratorWidth divisorWidth : Nat}
    (input : ClassicalAlgorithms.DivRem.Input
      numeratorWidth divisorWidth) :
    CShape.Value (InputShape numeratorWidth divisorWidth) :=
  .product (encodeWord input.numerator) (encodeWord input.divisor)

/-- Decode typed-machine division operands to the pure carrier. -/
def decodeInput {numeratorWidth divisorWidth : Nat}
    (input : CShape.Value (InputShape numeratorWidth divisorWidth)) :
    ClassicalAlgorithms.DivRem.Input
      numeratorWidth divisorWidth where
  numerator := decodeWord input.first
  divisor := decodeWord input.second

/-- Encode the pure quotient-and-remainder result for the typed machine. -/
def encodeOutput {numeratorWidth divisorWidth : Nat}
    (output : ClassicalAlgorithms.DivRem.Output
      numeratorWidth divisorWidth) :
    CShape.Value (OutputShape numeratorWidth divisorWidth) :=
  .product (encodeWord output.quotient) (encodeWord output.remainder)

/-- Decode the typed-machine quotient-and-remainder result. -/
def decodeOutput {numeratorWidth divisorWidth : Nat}
    (output : CShape.Value (OutputShape numeratorWidth divisorWidth)) :
    ClassicalAlgorithms.DivRem.Output
      numeratorWidth divisorWidth where
  quotient := decodeWord output.first
  remainder := decodeWord output.second

@[simp] theorem fixedWidthDivRem_decode_encode_input
    {numeratorWidth divisorWidth : Nat}
    (input : ClassicalAlgorithms.DivRem.Input
      numeratorWidth divisorWidth) :
    decodeInput (encodeInput input) = input := by
  cases input
  rfl

@[simp] theorem fixedWidthDivRem_encode_decode_input
    {numeratorWidth divisorWidth : Nat}
    (input : CShape.Value (InputShape numeratorWidth divisorWidth)) :
    encodeInput (decodeInput input) = input := by
  cases input with
  | product numerator divisor =>
      cases numerator
      cases divisor
      rfl

@[simp] theorem fixedWidthDivRem_decode_encode_output
    {numeratorWidth divisorWidth : Nat}
    (output : ClassicalAlgorithms.DivRem.Output
      numeratorWidth divisorWidth) :
    decodeOutput (encodeOutput output) = output := by
  cases output
  rfl

@[simp] theorem fixedWidthDivRem_encode_decode_output
    {numeratorWidth divisorWidth : Nat}
    (output : CShape.Value (OutputShape numeratorWidth divisorWidth)) :
    encodeOutput (decodeOutput output) = output := by
  cases output with
  | product quotient remainder =>
      cases quotient
      cases remainder
      rfl

/-- On valid input, Core division agrees completely with the public evaluator. -/
theorem fixedWidthDivRem_core_eval_bridge {numeratorWidth divisorWidth : Nat}
    (input : CShape.Value (InputShape numeratorWidth divisorWidth))
    (inputValid :
      ClassicalAlgorithms.DivRem.valid (decodeInput input)) :
    decodeOutput (CShape.divRem numeratorWidth divisorWidth input) =
      ClassicalAlgorithms.DivRem.eval
        (decodeInput input) inputValid := by
  cases input with
  | product numerator divisor =>
      cases numerator
      cases divisor
      rfl

/-- The retained cell read by the caller after the actual arithmetic instruction. -/
def resultRef {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (resultKey : StorageKey) (numeratorWidth divisorWidth : Nat) (fresh : resultKey ∉ ctx.keys) :
    CInputRef (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh)
      (OutputShape numeratorWidth divisorWidth) :=
  .storage (CStorageRef.retainedHead ctx resultKey (OutputShape numeratorWidth divisorWidth) fresh)

/-- One closed instruction reads the supplied operands and writes the fresh result cell. -/
def instruction {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    ClassicalOp (InputShape numeratorWidth divisorWidth) (OutputShape numeratorWidth divisorWidth)
      (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh)
        (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh) :=
  .divRem numeratorWidth divisorWidth (ctx.addRetained resultKey (OutputShape numeratorWidth
    divisorWidth) fresh)
    (input.underRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh)
    (CWriteRef.retainedHead ctx resultKey (OutputShape numeratorWidth divisorWidth) fresh)

/-- The composable native circuit allocates its result and executes the arithmetic operation. -/
def routine {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    Circuit ctx (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh) :=
  Circuit.retainedStep ctx resultKey (OutputShape numeratorWidth divisorWidth) fresh
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh)

/-- The actual store update appearing in the circuit execution equation. -/
def finalStore {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) : Execution.Store (ctx.addRetained resultKey (OutputShape
      numeratorWidth divisorWidth) fresh) :=
  (store.pushRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh).applyOp
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh)

/-- Reading the written cell gives the native arithmetic evaluator on the original operands. -/
theorem finalStore_read {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) :
    (finalStore ctx numeratorWidth divisorWidth input resultKey fresh store).read (resultRef
      ctx resultKey numeratorWidth divisorWidth fresh) =
      CShape.divRem numeratorWidth divisorWidth (store.read input) := by
  change ((store.pushRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh).applyOp
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh)).read
      (.storage (instruction ctx numeratorWidth divisorWidth input resultKey
        fresh).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.divRem numeratorWidth divisorWidth
    ((store.pushRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh).read
      (input.underRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh)) = _
  rw [Execution.Store.read_pushRetained_underRetained]

/-- The result of the actual store update agrees with the pure arithmetic specification. -/
theorem fixedWidthDivRem_eval_bridge {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx)
    (inputValid : ClassicalAlgorithms.DivRem.valid
      (decodeInput (store.read input))) :
    decodeOutput ((finalStore ctx numeratorWidth divisorWidth input resultKey fresh store).read
      (resultRef ctx resultKey numeratorWidth divisorWidth fresh)) =
        ClassicalAlgorithms.DivRem.eval (decodeInput (store.read input)) inputValid := by
  rw [finalStore_read]
  exact fixedWidthDivRem_core_eval_bridge (store.read input) inputValid

/-- Actual paths emit exactly the one native classical arithmetic event. -/
theorem fixedWidthDivRem_eventTrace_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx numeratorWidth divisorWidth input resultKey fresh).Path) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).eventTrace path =
      [(.classicalOperation (.divRem numeratorWidth divisorWidth) : Resource.Event kind)] := rfl

/-- The actual native event multiplicity has no separately supplied cost witness. -/
theorem fixedWidthDivRem_resourcePool_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx numeratorWidth divisorWidth input resultKey fresh).Path) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.divRem numeratorWidth divisorWidth)) := by
  change ResourcePool.ofList [(.classicalOperation (.divRem numeratorWidth divisorWidth) :
    Resource.Event kind)] = _
  simp

/-- The complete extended context determines the actual resident peak. -/
theorem fixedWidthDivRem_peakResidentSpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx numeratorWidth divisorWidth input resultKey fresh).Path) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).peakResidentSpace path =
      (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh).residentSpace :=
  Circuit.retainedStep_peakResidentSpace ctx resultKey (OutputShape numeratorWidth
    divisorWidth) fresh
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh) path

/-- The retained result is included in the actual auxiliary peak. -/
theorem fixedWidthDivRem_peakAuxiliarySpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx numeratorWidth divisorWidth input resultKey fresh).Path) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).peakAuxiliarySpace path =
      (ctx.addRetained resultKey (OutputShape numeratorWidth divisorWidth) fresh).auxiliarySpace :=
  Circuit.retainedStep_peakAuxiliarySpace ctx resultKey (OutputShape numeratorWidth
    divisorWidth) fresh
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh) path

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The common interpreter performs this update on complete states with any external reference. -/
theorem fixedWidthDivRem_execute {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).execute Reference state =
      state.mapClassical (fun value =>
        (finalStore ctx numeratorWidth divisorWidth input resultKey fresh value.1, (value.2,
          ((), ())))) :=
  Circuit.execute_retainedStep ctx resultKey (OutputShape numeratorWidth divisorWidth) fresh
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh) state

/-- Borrowed values and their full external quantum correlations survive the actual circuit. -/
theorem fixedWidthDivRem_borrowedRestored {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (numeratorWidth divisorWidth : Nat)
    (input : CInputRef ctx (InputShape numeratorWidth divisorWidth))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx numeratorWidth divisorWidth input resultKey fresh).BorrowedRestored Reference state
      ((routine ctx numeratorWidth divisorWidth input resultKey fresh).execute Reference state) :=
  Circuit.retainedStep_borrowedRestored ctx resultKey (OutputShape numeratorWidth divisorWidth)
    fresh
    (instruction ctx numeratorWidth divisorWidth input resultKey fresh) state

end

end QuantumAlg.ClassicalRoutines.DivRem
