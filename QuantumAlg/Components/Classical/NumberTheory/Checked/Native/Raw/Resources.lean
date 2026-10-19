/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Raw
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Depth
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Space
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Trace.Cost

/-!
# Actual widened-XGCD trace, durations and storage

The single original denominator resize precedes the exact actual raw-engine
trace. The reusable raw engine's independent slot and live-space bounds are
retained as bounds. The additional denominator workspace is a real allocation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalWorkspace XGCD.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original resize followed by the unchanged independent raw-engine event envelope. -/
lemma withWidenedXgcd_pool_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd (model := model) denominator modulus outputs).Path) :
    (withWidenedXgcd (model := model) denominator modulus outputs).resourcePool path ≤
      ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] +
        rawEnvelope model (width + 1) := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := BitWord.instruction (execution := model)
    (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine (model := model)
    (.product (transport.liftInput modulus) (GCD.cellRead widened)) (outputs.transport transport)
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  have head : first.eventTrace path.1 =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] :=
    BitWord.bitWord_instruction_eventTrace _ path.1
  rw [head, ResourcePool.ofList_append]
  exact add_le_add_right (xgcdNativeRawEngine_pool_le _ _ path.2) _

/-- The one real resize adds its duration to the original raw-engine schedule bound. -/
lemma withWidenedXgcd_depth_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (duration : Resource.Event model → Nat)
    (path : (withWidenedXgcd (model := model) denominator modulus outputs).Path) :
    (withWidenedXgcd (model := model) denominator modulus outputs).depth duration path ≤
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize
        width (width + 1)))) +
        rawDepthLimit (width + 1) duration := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := BitWord.instruction (execution := model)
    (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine (model := model)
    (.product (transport.liftInput modulus) (GCD.cellRead widened)) (outputs.transport transport)
  change first.depth duration path.1 + second.depth duration path.2 ≤ _
  have depth : first.depth duration path.1 =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))) :=
    BitWord.bitWord_instruction_depth _ duration path.1
  rw [depth]
  exact Nat.add_le_add_left (xgcdNativeRawEngine_depth_le _ _ duration path.2) _

/-- Every actual selected path remains serial, with duration exactly its own native event sum. -/
lemma withWidenedXgcd_duration_eventTrace
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (duration : Resource.Event model → Nat)
    (path : (withWidenedXgcd (model := model) denominator modulus outputs).Path) :
    (withWidenedXgcd (model := model) denominator modulus outputs).depth duration path =
      (((withWidenedXgcd (model := model) denominator modulus outputs).eventTrace path).map
        duration).sum := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := BitWord.instruction (execution := model)
    (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine (model := model)
    (.product (transport.liftInput modulus) (GCD.cellRead widened)) (outputs.transport transport)
  change first.depth duration path.1 + second.depth duration path.2 =
    ((first.eventTrace path.1 ++ second.eventTrace path.2).map duration).sum
  have head : first.eventTrace path.1 =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] :=
    BitWord.bitWord_instruction_eventTrace _ path.1
  have depth : first.depth duration path.1 =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))) :=
    BitWord.bitWord_instruction_depth _ duration path.1
  rw [head, depth]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  exact congrArg (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1)))) + ·)
    (xgcdNativeRawEngine_duration_eventTrace _ _ duration path.2)

/-- The actual resident bound includes the widened denominator throughout the complete raw run. -/
lemma withWidenedXgcd_resident_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd (model := model) denominator modulus outputs).Path) :
    (withWidenedXgcd (model := model) denominator modulus outputs).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace model.kind (width + 1) +
        ctx.residentSpace := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := BitWord.instruction (execution := model) (widenedDenominatorOp
    (transport.liftInput denominator) widened)
  let second := rawEngine (model := model) (.product (transport.liftInput modulus) (GCD.cellRead
    widened))
    (outputs.transport transport)
  have body : (Circuit.seq first second).peakResidentSpace path ≤
      rawScratchSpace model.kind (width + 1) + (widenedXgcdCtx ctx width).residentSpace := by
    refine (le_of_eq (Circuit.peakResidentSpace_seq first second path)).trans ?_
    apply SpacePool.max_le
    · exact (le_of_eq (Circuit.peakResidentSpace_classical
        (BitWord.selectedApplication (execution := model)
          (widenedDenominatorOp (transport.liftInput denominator) widened)) path.1)).trans
        (le_add_of_nonneg_left zero_le)
    · exact xgcdNativeRawEngine_resident_le _ _ path.2
  have outer := Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh (Circuit.seq first second) path
  refine (le_of_eq outer).trans (SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_)
  simpa only [widenedXgcdCtx, RuntimeCtx.residentSpace_addWorkspace,
    add_assoc, add_comm, add_left_comm] using body

/-- The auxiliary bound charges the same actual denominator and raw-engine workspaces. -/
lemma withWidenedXgcd_auxiliary_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd (model := model) denominator modulus outputs).Path) :
    (withWidenedXgcd (model := model) denominator modulus outputs).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace model.kind (width + 1) +
        ctx.auxiliarySpace := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := BitWord.instruction (execution := model) (widenedDenominatorOp
    (transport.liftInput denominator) widened)
  let second := rawEngine (model := model) (.product (transport.liftInput modulus) (GCD.cellRead
    widened))
    (outputs.transport transport)
  have body : (Circuit.seq first second).peakAuxiliarySpace path ≤
      rawScratchSpace model.kind (width + 1) + (widenedXgcdCtx ctx width).auxiliarySpace := by
    refine (le_of_eq (Circuit.peakAuxiliarySpace_seq first second path)).trans ?_
    apply SpacePool.max_le
    · exact (le_of_eq (Circuit.peakAuxiliarySpace_classical
        (BitWord.selectedApplication (execution := model)
          (widenedDenominatorOp (transport.liftInput denominator) widened)) path.1)).trans
        (le_add_of_nonneg_left zero_le)
    · exact xgcdNativeRawEngine_auxiliary_le _ _ path.2
  have outer := Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh (Circuit.seq first second) path
  refine (le_of_eq outer).trans (SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_)
  simpa only [widenedXgcdCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
    add_assoc, add_comm, add_left_comm] using body

/-- The same certified actual record emits the original unpadded widened-XGCD trace. -/
lemma withWidenedXgcd_record_eventTrace (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (distinct : outputs.Distinct)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (withWidenedXgcd
      (model := model) denominator modulus outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (withWidenedXgcd (model := model) denominator modulus outputs).execute
        environment Reference state =
        state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (store : Store ctx × model.HiddenState) :
    (withWidenedXgcd (model := model) denominator modulus outputs).eventTrace (record store).2 =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize width
        (width + 1)))] ++
        rawEvents model (widenedXgcdInput (store.1.read modulus) (store.1.read denominator)) := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let input := CInputRef.product (transport.liftInput modulus) (GCD.cellRead widened)
  let liftedOutputs := outputs.transport transport
  have liftedDistinct := xgcdNativeRawOutputs_distinct_transport outputs transport distinct
  obtain ⟨rawRecord, rawEquation, _⟩ := xgcdNativeRawEngine_actualRecord (model := model) input
    liftedOutputs
    liftedDistinct
  let first := BitWord.instruction (execution := model) (widenedDenominatorOp
    (transport.liftInput denominator) widened)
  let second := rawEngine (model := model) input liftedOutputs
  let firstRecord : Store (widenedXgcdCtx ctx width) × model.HiddenState →
      (Store (widenedXgcdCtx ctx width) × model.HiddenState) × first.Path := fun before =>
    let result := BitWord.instructionStep (execution := model)
      (widenedDenominatorOp (transport.liftInput denominator) widened) before.1
    ((result.1, before.2), result.2)
  let bodyRecord := Circuit.sequenceRecord first second firstRecord rawRecord
  have bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (widenedXgcdCtx ctx width) Reference (model.HiddenState × History)),
      (Circuit.seq first second).execute
        environment Reference state = state.mapClassical (fun entry =>
        let result := bodyRecord (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
    intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord
      (environment := environment) first second firstRecord rawRecord (by
      intro reference history historyFinite state
      refine (BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
        (widenedDenominatorOp (transport.liftInput denominator) widened) state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) rawEquation reference state
  let outerRecord := Circuit.workspaceRecord ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (Circuit.seq first second) bodyRecord
  have same := Circuit.executionRecord_unique (withWidenedXgcd (model := model) denominator
    modulus outputs) environment
    record outerRecord equation (Circuit.execute_workspaceRecord environment _ _ _
      (Circuit.seq first second) bodyRecord bodyEquation)
  rw [same]
  let entered := store.1.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh
  let enlarged := (firstRecord (entered, store.2)).1
  change first.eventTrace (firstRecord (entered, store.2)).2 ++
    (rawEngine (model := model) input liftedOutputs).eventTrace (rawRecord enlarged).2 = _
  have head : first.eventTrace (firstRecord (entered, store.2)).2 =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] :=
    BitWord.bitWord_instruction_eventTrace _ _
  rw [head]
  rw [xgcdNativeRawEngine_record_eventTrace input liftedOutputs liftedDistinct
    rawRecord rawEquation enlarged]
  have fresh : widened.key ∉ (transport.liftInput modulus).storageKeys := by
    rw [transport.liftInput_storageKeys]
    exact fun present => ctx.canonicalFreshKey_fresh (modulus.storageKeys_subset_context present)
  have enteredReads : transport.ReadsAs store.1 entered :=
    (Transport.id ctx).workspaceTransport_readsAs_pushWorkspace _ _ _
      (Transport.workspaceTransport_readsAs_id store.1)
  have modulusRead : enlarged.1.read (transport.liftInput modulus) = store.1.read modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys entered
      (widenedDenominatorOp (transport.liftInput denominator) widened) _ fresh).trans
        (enteredReads modulus)
  have denominatorRead : enlarged.1.read (GCD.cellRead widened) =
      CShape.wordResize (width + 1) (store.1.read denominator) :=
    (Store.read_applyOp_output entered
      (widenedDenominatorOp (transport.liftInput denominator) widened)).trans
        (congrArg (CShape.wordResize (width + 1))
          (enteredReads denominator))
  have inputRead : enlarged.1.read input =
      .product (store.1.read modulus) (CShape.wordResize (width + 1) (store.1.read denominator)) :=
    congrArg₂ CShape.Value.product modulusRead denominatorRead
  rw [inputRead]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
