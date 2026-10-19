/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Trace.Cost

/-!
# Exact public XGCD events from the same actual execution record

The raw engine contributes only its original genuine active steps. The five
public packing instructions follow those events. Real lexical allocation and
release retain this chronological trace, including zero events for inactive
scheduled slots, while every native operand width remains unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma public_actual_trace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (publicIntoResult (model := model) input result).execute environment Reference state =
          state.mapClassical (fun entry =>
            let actual := record (entry.1, entry.2.1)
            (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (publicIntoResult (model := model) input
        result).eventTrace (record before).2 =
        rawEvents model (GCD.decodeOperands (before.1.read input)) ++
          packingEvents model width := by
  let Trace (source : Store ctx) (events : List (Resource.Event model)) : Prop :=
    events = rawEvents model (GCD.decodeOperands (source.read input)) ++ packingEvents model width
  apply withCells_actualRecord_initialized_trace
    (environment := environment) ctx (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) Trace
  intro inner cells distinct transport _separated
  let outputs := publicRawOutputs cells
  let lifted := transport.liftInput input
  let target := transport.liftWrite result
  have outputDistinct := xgcdNativePublicRawOutputs_distinct cells distinct
  obtain ⟨rawRecord, rawEquation, _⟩ :=
    xgcdNativeRawEngine_actualRecord lifted outputs outputDistinct
  obtain ⟨packRecord, packEquation, _⟩ := xgcdNativePackRawOutputs_actualRecord outputs target
  refine ⟨Circuit.sequenceRecord (rawEngine (model := model) lifted outputs)
    (packRawOutputs (model := model) outputs target) rawRecord packRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord
      (environment := environment) (rawEngine (model := model) lifted outputs)
      (packRawOutputs (model := model) outputs target) rawRecord packRecord rawEquation
        packEquation reference state
  · intro source before reads _initialized
    change (rawEngine (model := model) lifted outputs).eventTrace (rawRecord before).2 ++
      (packRawOutputs (model := model) outputs target).eventTrace (packRecord (rawRecord
        before).1).2 = _
    rw [xgcdNativeRawEngine_record_eventTrace lifted outputs outputDistinct rawRecord rawEquation,
      xgcdNativePackRawOutputs_eventTrace]
    exact congrArg (fun value => rawEvents model (GCD.decodeOperands value) ++
      packingEvents model width) (reads input)

/-- Every certified actual public record has the original unpadded trace and five packing events. -/
lemma xgcdNativePublicIntoResult_record_eventTrace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (publicIntoResult (model := model) input result).execute environment
        Reference state = state.mapClassical
        (fun entry =>
          let actual := record (entry.1, entry.2.1)
          (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))))
    (store : Store ctx × model.HiddenState) :
    (publicIntoResult (model := model) input result).eventTrace (record store).2 =
      rawEvents model (GCD.decodeOperands (store.1.read input)) ++ packingEvents model width := by
  obtain ⟨actual, actualEquation, traced⟩ := public_actual_trace input result
  have same := Circuit.executionRecord_unique
    (environment := environment) (publicIntoResult (model := model) input result)
    record actual equation actualEquation
  rw [same]
  exact traced store

private lemma publicBody_duration_events
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width))
    (duration : Resource.Event model → Nat) (path : (publicBody (model := model) input outputs
      result).Path) :
    (publicBody (model := model) input outputs result).depth duration path =
      (((publicBody (model := model) input outputs result).eventTrace path).map duration).sum := by
  change (rawEngine (model := model) input outputs).depth duration path.1 +
    (packRawOutputs (model := model) outputs result).depth duration path.2 =
      (((rawEngine (model := model) input outputs).eventTrace path.1 ++
        (packRawOutputs (model := model) outputs result).eventTrace path.2).map duration).sum
  rw [List.map_append, List.sum_append, xgcdNativeRawEngine_duration_eventTrace,
    xgcdNativePackRawOutputs_depth, xgcdNativePackRawOutputs_eventTrace]

/-- The actual public serial path charges exactly its own complete event trace. -/
lemma xgcdNativePublicIntoResult_duration_eventTrace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (duration : Resource.Event model → Nat)
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).depth duration path =
      (((publicIntoResult (model := model) input result).eventTrace path).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => publicBody_duration_events _ _ _ duration selected) path

/-- Original genuine steps determine the exact arbitrary-duration cost of the same public record. -/
lemma xgcdNativePublicIntoResult_record_duration
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (publicIntoResult (model := model) input result).execute environment
        Reference state = state.mapClassical
        (fun entry =>
          let actual := record (entry.1, entry.2.1)
          (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))))
    (store : Store ctx × model.HiddenState)
    (duration : Resource.Event model → Nat) :
    (publicIntoResult (model := model) input result).depth duration (record store).2 =
      ((initializationEvents model width).map duration).sum +
        (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
          (GCD.decodeOperands (store.1.read input)) *
            ((activeEvents model width).map duration).sum +
          ((rawOutputEvents model width).map duration).sum) +
        ((packingEvents model width).map duration).sum := by
  rw [xgcdNativePublicIntoResult_duration_eventTrace,
    xgcdNativePublicIntoResult_record_eventTrace input result record equation,
    List.map_append, List.sum_append, xgcdNativeRawEvents_duration]

/-- Exactly fourteen operations per genuine step and fourteen setup, copy and packing operations. -/
lemma xgcdNativePublicIntoResult_record_unitDepth
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (publicIntoResult (model := model) input result).execute environment
        Reference state = state.mapClassical
        (fun entry =>
          let actual := record (entry.1, entry.2.1)
          (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))))
    (store : Store ctx × model.HiddenState) :
    (publicIntoResult (model := model) input result).depth (fun _ => 1) (record store).2 =
      14 * ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
        (GCD.decodeOperands (store.1.read input)) + 14 := by
  rw [xgcdNativePublicIntoResult_duration_eventTrace,
    xgcdNativePublicIntoResult_record_eventTrace input result record equation,
    List.map_append, List.sum_append, xgcdNativeRawEvents_unit_duration]
  change 14 * _ + 9 + 5 = _
  omega

/-- The same actual public record keeps every original native event coordinate and step count. -/
lemma xgcdNativePublicIntoResult_record_resourcePool
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (publicIntoResult (model := model) input result).execute environment
        Reference state = state.mapClassical
        (fun entry =>
          let actual := record (entry.1, entry.2.1)
          (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))))
    (store : Store ctx × model.HiddenState) :
    (publicIntoResult (model := model) input result).resourcePool (record store).2 =
      ResourcePool.ofList (initializationEvents model width) +
        (ResourcePool.scale (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
          (GCD.decodeOperands (store.1.read input))) (ResourcePool.ofList (activeEvents model
            width)) +
          ResourcePool.ofList (rawOutputEvents model width)) +
        ResourcePool.ofList (packingEvents model width) := by
  rw [Circuit.resourcePool,
    xgcdNativePublicIntoResult_record_eventTrace input result record equation,
    ResourcePool.ofList_append, xgcdNativeRawEvents_resourcePool]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
