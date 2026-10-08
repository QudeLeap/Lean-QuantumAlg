/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Core.Base.Classical.Value
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Exact original three-copy exposure updates

The actual status, candidate and reconstruction copies retain their original
chronological order. Complete-state equations allow arbitrary destination
aliasing. When actual internal sources avoid the earlier copy destinations,
the final Store is the exact three successive writes of those source values.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Three chronological destination writes preserve their actual overwrite behavior on aliases. -/
@[expose] public def exposureWrite (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
    (before : Store ctx)
    (value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape width))) : Store ctx :=
  ((before.write inverseSuccess value.first).write candidate value.second.first).write
    reconstruction value.second.second

/-- The original actual native copies thread the complete Store in order. -/
def exposureCopyStore (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx) : Store ctx :=
  ((before.applyOp (.bit .copy ctx success inverseSuccess)).applyOp
    (.wordUnary .copy width ctx recoveredCandidate candidate)).applyOp
      (.bit .copy ctx verified reconstruction)

/-- Complete actual three-copy execution preserves all quantum-reference blocks and history. -/
theorem exposureCopyBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (exposureCopyBody (model := model) success recoveredCandidate verified inverseSuccess candidate
      reconstruction).execute Reference state = state.mapClassical (fun entry =>
        let result := exposureCopyStep (model := model) success recoveredCandidate verified
          inverseSuccess candidate reconstruction entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [exposureCopyBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Source protection gives the exact three writes even when caller destinations alias. -/
theorem exposureCopyStore_write (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx)
    (candidateFree : inverseSuccess.key ∉ recoveredCandidate.storageKeys)
    (verifiedSuccessFree : inverseSuccess.key ∉ verified.storageKeys)
    (verifiedCandidateFree : candidate.key ∉ verified.storageKeys) :
    exposureCopyStore success recoveredCandidate verified inverseSuccess candidate reconstruction
      before = exposureWrite inverseSuccess candidate reconstruction before
        (.product (before.read success) (.product (before.read recoveredCandidate)
          (before.read verified))) := by
  change ((before.write inverseSuccess (before.read success)).write candidate
    ((before.write inverseSuccess (before.read success)).read recoveredCandidate)).write
      reconstruction
      (((before.write inverseSuccess (before.read success)).write candidate
        ((before.write inverseSuccess (before.read success)).read recoveredCandidate)).read
          verified) = _
  rw [Store.read_write_of_not_mem_storageKeys _ _ _ recoveredCandidate candidateFree,
    Store.read_write_of_not_mem_storageKeys _ _ _ verified verifiedCandidateFree,
    Store.read_write_of_not_mem_storageKeys _ _ _ verified verifiedSuccessFree]
  rfl

/-- All structural reads outside the three actual copy destinations remain unchanged. -/
theorem exposureCopyStore_read_other (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (successFree : inverseSuccess.key ∉ other.storageKeys)
    (candidateFree : candidate.key ∉ other.storageKeys)
    (reconstructionFree : reconstruction.key ∉ other.storageKeys) :
    (exposureCopyStore success recoveredCandidate verified inverseSuccess candidate reconstruction
      before).read other = before.read other := by
  unfold exposureCopyStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (.bit .copy ctx verified reconstruction)
    other reconstructionFree]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (.wordUnary .copy width ctx recoveredCandidate candidate) other candidateFree]
  exact Store.read_applyOp_of_not_mem_storageKeys _ (.bit .copy ctx success inverseSuccess)
    other successFree

/-- Exact chronological exposure writes preserve every other original caller read. -/
theorem exposureWrite_read_other (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width)) (reconstruction : CWriteRef ctx .bit)
    (before : Store ctx)
    (value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape width)))
    {shape : CShape} (other : CInputRef ctx shape)
    (successFree : inverseSuccess.key ∉ other.storageKeys)
    (candidateFree : candidate.key ∉ other.storageKeys)
    (reconstructionFree : reconstruction.key ∉ other.storageKeys) :
    (exposureWrite inverseSuccess candidate reconstruction before value).read other =
      before.read other := by
  unfold exposureWrite
  rw [Store.read_write_of_not_mem_storageKeys _ _ _ other reconstructionFree,
    Store.read_write_of_not_mem_storageKeys _ _ _ other candidateFree,
    Store.read_write_of_not_mem_storageKeys _ _ _ other successFree]

/-- Actual structural transport carries all three writes and their overwrite order exactly. -/
theorem exposureWrite_readsAs {outer : RuntimeCtx kind}
    (transport : ClassicalWorkspace.Transport outer ctx)
    (inverseSuccess : CWriteRef outer .bit) (candidate : CWriteRef outer (.unsignedWord width))
    (reconstruction : CWriteRef outer .bit) (source : Store outer) (before : Store ctx)
    (reads : transport.ReadsAs source before)
    (value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape width))) :
    transport.ReadsAs (exposureWrite inverseSuccess candidate reconstruction source value)
      (exposureWrite (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction) before value) := by
  unfold exposureWrite
  exact transport.workspaceTransport_readsAs_write
    (transport.workspaceTransport_readsAs_write
      (transport.workspaceTransport_readsAs_write reads inverseSuccess value.first)
      candidate value.second.first) reconstruction value.second.second

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
