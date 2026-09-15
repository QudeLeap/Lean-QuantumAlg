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

/-! Native retained-result AddCarry circuit and its exact arithmetic bridge. -/

namespace QuantumAlg.ClassicalRoutines.AddCarry

/-- Closed operand shape for equal-width addition. -/
public abbrev InputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- Closed result shape for the low word and carry bit. -/
public abbrev OutputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) .bit

/-- Encode the pure addition operands for the typed machine. -/
def encodeInput {width : Nat}
    (input : ClassicalAlgorithms.AddCarry.Input width) :
    CShape.Value (InputShape width) :=
  .product (encodeWord input.left) (encodeWord input.right)

/-- Decode typed-machine addition operands to the pure carrier. -/
def decodeInput {width : Nat} (input : CShape.Value (InputShape width)) :
    ClassicalAlgorithms.AddCarry.Input width where
  left := decodeWord input.first
  right := decodeWord input.second

/-- Encode the pure low-word-and-carry result for the typed machine. -/
def encodeOutput {width : Nat}
    (output : ClassicalAlgorithms.AddCarry.Output width) :
    CShape.Value (OutputShape width) :=
  .product (encodeWord output.low) (.bit output.carry)

/-- Decode the typed-machine low-word-and-carry result. -/
def decodeOutput {width : Nat} (output : CShape.Value (OutputShape width)) :
    ClassicalAlgorithms.AddCarry.Output width where
  low := decodeWord output.first
  carry := output.second.toBool

@[simp] theorem fixedWidthAddCarry_decode_encode_input {width : Nat}
    (input : ClassicalAlgorithms.AddCarry.Input width) :
    decodeInput (encodeInput input) = input := by
  cases input
  rfl

@[simp] theorem fixedWidthAddCarry_encode_decode_input {width : Nat}
    (input : CShape.Value (InputShape width)) :
    encodeInput (decodeInput input) = input := by
  cases input with
  | product left right =>
      cases left
      cases right
      rfl

@[simp] theorem fixedWidthAddCarry_decode_encode_output {width : Nat}
    (output : ClassicalAlgorithms.AddCarry.Output width) :
    decodeOutput (encodeOutput output) = output := by
  cases output
  rfl

@[simp] theorem fixedWidthAddCarry_encode_decode_output {width : Nat}
    (output : CShape.Value (OutputShape width)) :
    encodeOutput (decodeOutput output) = output := by
  cases output with
  | product low carry =>
      cases low
      cases carry
      rfl

/-- The Core addition instruction and the pure evaluator agree completely. -/
theorem fixedWidthAddCarry_core_eval_bridge {width : Nat}
    (input : CShape.Value (InputShape width)) :
    decodeOutput (CShape.addCarry width input) =
      ClassicalAlgorithms.AddCarry.eval (decodeInput input) := by
  cases input with
  | product left right =>
      cases left
      cases right
      rfl

/-- The retained cell read by the caller after the actual arithmetic instruction. -/
def resultRef {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (resultKey : StorageKey) (width : Nat) (fresh : resultKey ∉ ctx.keys) :
    CInputRef (ctx.addRetained resultKey (OutputShape width) fresh) (OutputShape width) :=
  .storage (CStorageRef.retainedHead ctx resultKey (OutputShape width) fresh)

/-- One closed instruction reads the supplied operands and writes the fresh result cell. -/
def instruction {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    ClassicalOp (InputShape width) (OutputShape width)
      (ctx.addRetained resultKey (OutputShape width) fresh) (ctx.addRetained resultKey
        (OutputShape width) fresh) :=
  .addCarry width (ctx.addRetained resultKey (OutputShape width) fresh)
    (input.underRetained resultKey (OutputShape width) fresh)
    (CWriteRef.retainedHead ctx resultKey (OutputShape width) fresh)

/-- The composable native circuit allocates its result and executes the arithmetic operation. -/
def routine {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys) :
    Circuit ctx (ctx.addRetained resultKey (OutputShape width) fresh) :=
  Circuit.retainedStep ctx resultKey (OutputShape width) fresh
    (instruction ctx width input resultKey fresh)

/-- The actual store update appearing in the circuit execution equation. -/
def finalStore {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) : Execution.Store (ctx.addRetained resultKey (OutputShape
      width) fresh) :=
  (store.pushRetained resultKey (OutputShape width) fresh).applyOp
    (instruction ctx width input resultKey fresh)

/-- Reading the written cell gives the native arithmetic evaluator on the original operands. -/
theorem finalStore_read {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) :
    (finalStore ctx width input resultKey fresh store).read (resultRef ctx resultKey width fresh) =
      CShape.addCarry width (store.read input) := by
  change ((store.pushRetained resultKey (OutputShape width) fresh).applyOp
    (instruction ctx width input resultKey fresh)).read
      (.storage (instruction ctx width input resultKey fresh).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.addCarry width
    ((store.pushRetained resultKey (OutputShape width) fresh).read
      (input.underRetained resultKey (OutputShape width) fresh)) = _
  rw [Execution.Store.read_pushRetained_underRetained]

/-- The result of the actual store update agrees with the pure arithmetic specification. -/
theorem fixedWidthAddCarry_eval_bridge {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (store : Execution.Store ctx) :
    decodeOutput ((finalStore ctx width input resultKey fresh store).read
      (resultRef ctx resultKey width fresh)) =
        ClassicalAlgorithms.AddCarry.eval (decodeInput (store.read input)) := by
  rw [finalStore_read]
  exact fixedWidthAddCarry_core_eval_bridge (store.read input)

/-- Actual paths emit exactly the one native classical arithmetic event. -/
theorem fixedWidthAddCarry_eventTrace_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx width input resultKey fresh).Path) :
    (routine ctx width input resultKey fresh).eventTrace path =
      [(.classicalOperation (.addCarry width) : Resource.Event kind)] := rfl

/-- The actual native event multiplicity has no separately supplied cost witness. -/
theorem fixedWidthAddCarry_resourcePool_eq_singleton {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx width input resultKey fresh).Path) :
    (routine ctx width input resultKey fresh).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.addCarry width)) := by
  change ResourcePool.ofList [(.classicalOperation (.addCarry width) : Resource.Event kind)] = _
  simp

/-- The complete extended context determines the actual resident peak. -/
theorem fixedWidthAddCarry_peakResidentSpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx width input resultKey fresh).Path) :
    (routine ctx width input resultKey fresh).peakResidentSpace path =
      (ctx.addRetained resultKey (OutputShape width) fresh).residentSpace :=
  Circuit.retainedStep_peakResidentSpace ctx resultKey (OutputShape width) fresh
    (instruction ctx width input resultKey fresh) path

/-- The retained result is included in the actual auxiliary peak. -/
theorem fixedWidthAddCarry_peakAuxiliarySpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    (path : (routine ctx width input resultKey fresh).Path) :
    (routine ctx width input resultKey fresh).peakAuxiliarySpace path =
      (ctx.addRetained resultKey (OutputShape width) fresh).auxiliarySpace :=
  Circuit.retainedStep_peakAuxiliarySpace ctx resultKey (OutputShape width) fresh
    (instruction ctx width input resultKey fresh) path

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The common interpreter performs this update on complete states with any external reference. -/
theorem fixedWidthAddCarry_execute {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx width input resultKey fresh).execute Reference state =
      state.mapClassical (fun value =>
        (finalStore ctx width input resultKey fresh value.1, (value.2, ((), ())))) :=
  Circuit.execute_retainedStep ctx resultKey (OutputShape width) fresh
    (instruction ctx width input resultKey fresh) state

/-- Borrowed values and their full external quantum correlations survive the actual circuit. -/
theorem fixedWidthAddCarry_borrowedRestored {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat)
    (input : CInputRef ctx (InputShape width))
    (resultKey : StorageKey) (fresh : resultKey ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (routine ctx width input resultKey fresh).BorrowedRestored Reference state
      ((routine ctx width input resultKey fresh).execute Reference state) :=
  Circuit.retainedStep_borrowedRestored ctx resultKey (OutputShape width) fresh
    (instruction ctx width input resultKey fresh) state

end

end QuantumAlg.ClassicalRoutines.AddCarry
