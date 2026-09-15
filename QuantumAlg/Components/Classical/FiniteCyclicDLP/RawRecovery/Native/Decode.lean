/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
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
def measuredDecodeBody (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) :
    Circuit (decodeCtx ctx count) (decodeCtx ctx count) :=
  .seq (.classical (measuredPackOp input))
    (TerminalDecode.into .bigEndian (packedInput ctx count) (writeUnderDecode decoded count))

/-- Actual complete decoder with the packing allocation and its matching release. -/
def measuredDecodeInto (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh
    (measuredDecodeBody input decoded)

/-- Real sequential store and branch path inside the packing scope. -/
def measuredDecodeBodyStep (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store (decodeCtx ctx count)) :
    Store (decodeCtx ctx count) × (measuredDecodeBody input decoded).Path :=
  let packed := store.applyOp (measuredPackOp input)
  let later := TerminalDecode.foldStep (writeUnderDecode decoded count)
    (List.ofFn (fun index => CInputRef.bitsGet (packedInput ctx count) index)) packed
  (later.1, ((), later.2))

/-- Real outer-store update after releasing the exact lexical packing head. -/
def measuredDecodeStep (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx) :
    Store ctx × (measuredDecodeInto input decoded).Path :=
  let result := measuredDecodeBodyStep input decoded
    (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh result.1,
    result.2)

/-- Literal pack and decoder execution retain every complete quantum-reference block. -/
theorem measuredDecodeBody_execute (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (decodeCtx ctx count) Reference History) :
    (measuredDecodeBody input decoded).execute Reference state =
      state.mapClassical (fun entry =>
        ((measuredDecodeBodyStep input decoded entry.1).1,
          (entry.2, (measuredDecodeBodyStep input decoded entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (measuredPackOp input))
    (TerminalDecode.into .bigEndian (packedInput ctx count) (writeUnderDecode decoded count))
    (fun store => (store.applyOp (measuredPackOp input), ()))
    (TerminalDecode.foldStep (writeUnderDecode decoded count)
      (List.ofFn (fun index => CInputRef.bitsGet (packedInput ctx count) index)))
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical (measuredPackOp input)
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (TerminalDecode.terminalDecode_fold_execute (writeUnderDecode decoded count) _
        reference initial).trans ?_
      congr 1)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete native decoder acts on actual stores and records its actual finite path. -/
theorem measuredDecodeInto_execute (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (measuredDecodeInto input decoded).execute Reference state =
      state.mapClassical (fun entry =>
        ((measuredDecodeStep input decoded entry.1).1,
          (entry.2, (measuredDecodeStep input decoded entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh (measuredDecodeBody input decoded)
    (measuredDecodeBodyStep input decoded) (measuredDecodeBody_execute input decoded)
    Reference state).trans ?_
  congr 1

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

private theorem measuredDecodeBody_read_output
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store (decodeCtx ctx count)) :
    ((measuredDecodeBodyStep input decoded store).1.read
      (TerminalDecode.writeInput (writeUnderDecode decoded count))).toNat =
        (ClassicalAlgorithms.TerminalDecode.eval
          (measuredDecodeInput (store.read (underDecode input count)))).val := by
  have result := TerminalDecode.terminalDecode_intoFromBitRefs_read_output
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
theorem measuredDecodeInto_read_output (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx) :
    ((measuredDecodeStep input decoded store).1.read (TerminalDecode.writeInput decoded)).toNat =
      (ClassicalAlgorithms.TerminalDecode.eval (measuredDecodeInput (store.read input))).val := by
  have exitRead := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh
    (measuredDecodeBodyStep input decoded
      (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)).1
    (TerminalDecode.writeInput decoded)
  have decodedValue := measuredDecodeBody_read_output input decoded
    (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)
  have source := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh input
  exact (congrArg CShape.Value.toNat exitRead).trans
    (decodedValue.trans (congrArg (fun value =>
      (ClassicalAlgorithms.TerminalDecode.eval (measuredDecodeInput value)).val) source))

/-- All original structural reads outside the decoded output remain unchanged. -/
theorem measuredDecodeInto_read_other (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : decoded.key ∉ other.storageKeys) :
    (measuredDecodeStep input decoded store).1.read other = store.read other := by
  have exitRead := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh
    (measuredDecodeBodyStep input decoded
      (store.pushWorkspace ctx.canonicalFreshKey (.bits count) ctx.canonicalFreshKey_fresh)).1 other
  have folded := TerminalDecode.terminalDecode_fold_read_other (writeUnderDecode decoded count)
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
