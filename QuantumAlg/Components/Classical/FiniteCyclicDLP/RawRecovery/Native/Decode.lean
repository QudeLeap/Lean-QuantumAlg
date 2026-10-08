/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Native decoding of actual finite binary measurement cells

One charged packing instruction materializes the measured binary values in a
fresh lexical bit cell. The existing big-endian decoder then writes the actual
unsigned output and the matching scope releases the packed cell. The output
may have any initial value and may occur in the original structural input:
all source values have already been packed before the first output write.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}

/-- The one actual lexical cell holds the ordered packed binary values. -/
@[reducible] def decodeCtx (ctx : RuntimeCtx kind) (count : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh

/-- Existing structural inputs retain their identities under the packing scope. -/
def underDecode {shape : CShape} (input : CInputRef ctx shape) (count : Nat) :
    CInputRef (decodeCtx ctx count) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh

/-- The output is the same existing writable word under the fresh scope. -/
def writeUnderDecode {shape : CShape} (output : CWriteRef ctx shape) (count : Nat) :
    CWriteRef (decodeCtx ctx count) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh

/-- Actual writable head of the lexical packing scope. -/
def packedCell (ctx : RuntimeCtx kind) (count : Nat) :
    CWriteRef (decodeCtx ctx count) (.bits count) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh

/-- Structural read of that actual packing cell. -/
def packedInput (ctx : RuntimeCtx kind) (count : Nat) :
    CInputRef (decodeCtx ctx count) (.bits count) :=
  .storage (packedCell ctx count).toCStorageRef

/-- The closed native instruction reads all measured values before any output write. -/
def measuredPackOp (input : CInputRef ctx (.fixedVector count (.finite 2))) :
    ClassicalOp (.fixedVector count (.finite 2)) (.bits count)
      (decodeCtx ctx count) (decodeCtx ctx count) :=
  .packFiniteBits count (decodeCtx ctx count) (underDecode input count) (packedCell ctx count)

/-- Pack, then run the original literal big-endian shift-and-increment decoder. -/
def measuredDecodeBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) :
    Circuit model (decodeCtx ctx count) (decodeCtx ctx count) :=
  .seq (BitWord.instruction (execution := model) (measuredPackOp input))
    (TerminalDecode.into (model := model) .bigEndian
      (packedInput ctx count) (writeUnderDecode decoded count))

/-- Actual complete decoder with the packing allocation and its matching release. -/
def measuredDecodeInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh
    (measuredDecodeBody (model := model) input decoded)

/-- Real sequential store and branch path inside the packing scope. -/
def measuredDecodeBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store (decodeCtx ctx count)) :
    Store (decodeCtx ctx count) × (measuredDecodeBody (model := model) input decoded).Path :=
  let packed := BitWord.instructionStep (execution := model) (measuredPackOp input) store
  let later := TerminalDecode.foldStep (model := model) (writeUnderDecode decoded count)
    (List.ofFn (fun index => CInputRef.bitsGet (packedInput ctx count) index)) packed.1
  (later.1, (packed.2, later.2))

/-- Real outer-store update after releasing the exact lexical packing head. -/
def measuredDecodeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx) :
    Store ctx × (measuredDecodeInto (model := model) input decoded).Path :=
  let result := measuredDecodeBodyStep (model := model) input decoded
    (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh result.1,
    result.2)

/-- Literal packing and decoding preserve the complete service/reference record. -/
theorem measuredDecodeBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (decodeCtx ctx count) Reference (model.HiddenState × History)) :
    (measuredDecodeBody (model := model) input decoded).execute Reference state =
      state.mapClassical (fun entry =>
        let result := measuredDecodeBodyStep (model := model) input decoded entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (measuredPackOp input))
    (TerminalDecode.into (model := model) .bigEndian
      (packedInput ctx count) (writeUnderDecode decoded count))
    (fun before =>
      let result := BitWord.instructionStep (execution := model) (measuredPackOp input) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := TerminalDecode.foldStep (model := model) (writeUnderDecode decoded count)
        (List.ofFn (fun index => CInputRef.bitsGet (packedInput ctx count) index)) before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute (execution := model) (measuredPackOp input)
      initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (TerminalDecode.terminalDecode_fold_execute (model := model)
      (writeUnderDecode decoded count) _ reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Releasing the packed cell retains the actual native path and full service state. -/
theorem measuredDecodeInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (measuredDecodeInto (model := model) input decoded).execute Reference state =
      state.mapClassical (fun entry =>
        let result := measuredDecodeStep (model := model) input decoded entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh (measuredDecodeBody (model := model) input decoded)
    (fun before =>
      let result := measuredDecodeBodyStep (model := model) input decoded before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (measuredDecodeBody_execute (model := model) input decoded reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The mathematical binary sequence is only a specification of the actual packing output. -/
def measuredDecodeInput (value : CShape.Value (.fixedVector count (.finite 2))) :
    ClassicalAlgorithms.TerminalDecode.Input count :=
  ⟨.bigEndian, fun index => decide ((value.get index).toFin.val = 1)⟩

private theorem decoded_key_ne_fresh (decoded : CWriteRef ctx (.unsignedWord count)) :
    decoded.key ≠ ctx.canonicalFreshKey := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem decoded.toCStorageRef.present

private theorem measuredDecodeBody_read_output {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store (decodeCtx ctx count)) :
    ((measuredDecodeBodyStep (model := model) input decoded store).1.read
      (TerminalDecode.writeInput (writeUnderDecode decoded count))).toNat =
        (ClassicalAlgorithms.TerminalDecode.eval
          (measuredDecodeInput (store.read (underDecode input count)))).val := by
  have result := TerminalDecode.terminalDecode_intoFromBitRefs_read_output (model := model)
    .bigEndian (fun index => CInputRef.bitsGet (packedInput ctx count) index)
    (writeUnderDecode decoded count) (store.applyOp (measuredPackOp input)) (by
      intro index
      change decoded.key ∉ [ctx.canonicalFreshKey]
      exact fun member => decoded_key_ne_fresh decoded (List.mem_singleton.mp member))
  have source : TerminalDecode.decodeInputFromBitRefs .bigEndian
      (store.applyOp (measuredPackOp input))
      (fun index => CInputRef.bitsGet (packedInput ctx count) index) =
        measuredDecodeInput (store.read (underDecode input count)) := by
    apply congrArg (ClassicalAlgorithms.TerminalDecode.Input.mk .bigEndian)
    funext index
    change (((store.applyOp (measuredPackOp input)).read (packedInput ctx count)).bitGet
      index).toBool = _
    exact (congrArg (fun value : CShape.Value (.bits count) => (value.bitGet index).toBool)
      (Store.read_applyOp_output store (measuredPackOp input))).trans rfl
  exact result.trans (congrArg (fun value =>
    (ClassicalAlgorithms.TerminalDecode.eval value).val) source)

/-- The actual decoded word equals the original big-endian value, for every initial store. -/
theorem measuredDecodeInto_read_output {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx) :
    ((measuredDecodeStep (model := model) input decoded store).1.read
      (TerminalDecode.writeInput decoded)).toNat =
      (ClassicalAlgorithms.TerminalDecode.eval (measuredDecodeInput (store.read input))).val := by
  have exitRead := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh
    (measuredDecodeBodyStep (model := model) input decoded
      (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)).1
    (TerminalDecode.writeInput decoded)
  have decodedValue := measuredDecodeBody_read_output (model := model) input decoded
    (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)
  have source := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh input
  exact (congrArg CShape.Value.toNat exitRead).trans
    (decodedValue.trans (congrArg (fun value =>
      (ClassicalAlgorithms.TerminalDecode.eval (measuredDecodeInput value)).val) source))

/-- All original structural reads outside the decoded output remain unchanged. -/
theorem measuredDecodeInto_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : decoded.key ∉ other.storageKeys) :
    (measuredDecodeStep (model := model) input decoded store).1.read other = store.read other := by
  have exitRead := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh
    (measuredDecodeBodyStep (model := model) input decoded
      (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)).1 other
  have folded := TerminalDecode.terminalDecode_fold_read_other (model := model)
    (writeUnderDecode decoded count)
    (List.ofFn (fun index => CInputRef.bitsGet (packedInput ctx count) index))
    ((store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh).applyOp
      (measuredPackOp input)) (underDecode other count) (by
        change decoded.key ∉ (underDecode other count).storageKeys
        simpa only [underDecode, CInputRef.storageKeys_underWorkspace] using separate)
  have packed := Store.read_applyOp_of_not_mem_storageKeys
    (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)
    (measuredPackOp input) (underDecode other count) (by
      change ctx.canonicalFreshKey ∉
        (other.underWorkspace ctx.canonicalFreshKey (.bits count)
          ctx.canonicalFreshKey_fresh).storageKeys
      rw [CInputRef.storageKeys_underWorkspace]
      exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present))
  exact exitRead.trans (folded.trans (packed.trans
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.bits count)
      ctx.canonicalFreshKey_fresh other)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
