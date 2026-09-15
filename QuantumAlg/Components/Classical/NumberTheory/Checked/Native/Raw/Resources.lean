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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original resize followed by the unchanged independent raw-engine event envelope. -/
theorem withWidenedXgcd_pool_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd denominator modulus outputs).Path) :
    (withWidenedXgcd denominator modulus outputs).resourcePool path ≤
      ResourcePool.ofList [.classicalOperation (.wordResize width (width + 1))] +
        rawEnvelope kind (width + 1) := by
  change ResourcePool.ofList ([.classicalOperation (.wordResize width (width + 1))] ++
    (rawEngine _ _).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add_right (xgcdNativeRawEngine_pool_le _ _ path.2) _

/-- The one real resize adds its duration to the original raw-engine schedule bound. -/
theorem withWidenedXgcd_depth_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (duration : Resource.Event kind → Nat)
    (path : (withWidenedXgcd denominator modulus outputs).Path) :
    (withWidenedXgcd denominator modulus outputs).depth duration path ≤
      duration (.classicalOperation (.wordResize width (width + 1))) +
        rawDepthLimit (width + 1) duration := by
  change duration (.classicalOperation (.wordResize width (width + 1))) +
    (rawEngine _ _).depth duration path.2 ≤ _
  exact Nat.add_le_add_left (xgcdNativeRawEngine_depth_le _ _ duration path.2) _

/-- Every actual selected path remains serial, with duration exactly its own native event sum. -/
theorem withWidenedXgcd_duration_eventTrace
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (duration : Resource.Event kind → Nat)
    (path : (withWidenedXgcd denominator modulus outputs).Path) :
    (withWidenedXgcd denominator modulus outputs).depth duration path =
      (((withWidenedXgcd denominator modulus outputs).eventTrace path).map duration).sum := by
  change duration (.classicalOperation (.wordResize width (width + 1))) +
    (rawEngine _ _).depth duration path.2 =
      duration (.classicalOperation (.wordResize width (width + 1))) +
        (((rawEngine _ _).eventTrace path.2).map duration).sum
  exact congrArg (duration (.classicalOperation (.wordResize width (width + 1))) + ·)
    (xgcdNativeRawEngine_duration_eventTrace _ _ duration path.2)

/-- The actual resident bound includes the widened denominator throughout the complete raw run. -/
theorem withWidenedXgcd_resident_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd denominator modulus outputs).Path) :
    (withWidenedXgcd denominator modulus outputs).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace kind (width + 1) +
        ctx.residentSpace := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := Circuit.classical (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine (.product (transport.liftInput modulus) (GCD.cellRead widened))
    (outputs.transport transport)
  have body : (Circuit.seq first second).peakResidentSpace path ≤
      rawScratchSpace kind (width + 1) + (widenedXgcdCtx ctx width).residentSpace := by
    refine (le_of_eq (Circuit.peakResidentSpace_seq first second path)).trans ?_
    apply SpacePool.max_le
    · exact (le_of_eq (Circuit.peakResidentSpace_classical _ path.1)).trans
        (le_add_of_nonneg_left zero_le)
    · exact xgcdNativeRawEngine_resident_le _ _ path.2
  have outer := Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh (Circuit.seq first second) path
  refine (le_of_eq outer).trans (SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_)
  simpa only [widenedXgcdCtx, RuntimeCtx.residentSpace_addWorkspace,
    add_assoc, add_comm, add_left_comm] using body

/-- The auxiliary bound charges the same actual denominator and raw-engine workspaces. -/
theorem withWidenedXgcd_auxiliary_le (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (path : (withWidenedXgcd denominator modulus outputs).Path) :
    (withWidenedXgcd denominator modulus outputs).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) + rawScratchSpace kind (width + 1) +
        ctx.auxiliarySpace := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let first := Circuit.classical (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine (.product (transport.liftInput modulus) (GCD.cellRead widened))
    (outputs.transport transport)
  have body : (Circuit.seq first second).peakAuxiliarySpace path ≤
      rawScratchSpace kind (width + 1) + (widenedXgcdCtx ctx width).auxiliarySpace := by
    refine (le_of_eq (Circuit.peakAuxiliarySpace_seq first second path)).trans ?_
    apply SpacePool.max_le
    · exact (le_of_eq (Circuit.peakAuxiliarySpace_classical _ path.1)).trans
        (le_add_of_nonneg_left zero_le)
    · exact xgcdNativeRawEngine_auxiliary_le _ _ path.2
  have outer := Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh (Circuit.seq first second) path
  refine (le_of_eq outer).trans (SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_)
  simpa only [widenedXgcdCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
    add_assoc, add_comm, add_left_comm] using body

/-- The same certified actual record emits the original unpadded widened-XGCD trace. -/
theorem withWidenedXgcd_record_eventTrace (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (distinct : outputs.Distinct)
    (record : Store ctx → Store ctx × (withWidenedXgcd denominator modulus outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (withWidenedXgcd denominator modulus outputs).execute Reference state =
        state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2))))
    (store : Store ctx) :
    (withWidenedXgcd denominator modulus outputs).eventTrace (record store).2 =
      [.classicalOperation (.wordResize width (width + 1))] ++
        rawEvents kind (widenedXgcdInput (store.read modulus) (store.read denominator)) := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let input := CInputRef.product (transport.liftInput modulus) (GCD.cellRead widened)
  let liftedOutputs := outputs.transport transport
  have liftedDistinct := xgcdNativeRawOutputs_distinct_transport outputs transport distinct
  obtain ⟨rawRecord, rawEquation, _⟩ := xgcdNativeRawEngine_actualRecord input liftedOutputs
    liftedDistinct
  let first := Circuit.classical (widenedDenominatorOp (transport.liftInput denominator) widened)
  let second := rawEngine input liftedOutputs
  let firstRecord : Store (widenedXgcdCtx ctx width) →
      Store (widenedXgcdCtx ctx width) × first.Path := fun before =>
    (before.applyOp (widenedDenominatorOp (transport.liftInput denominator) widened), ())
  let bodyRecord := Circuit.sequenceRecord first second firstRecord rawRecord
  have bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (widenedXgcdCtx ctx width) Reference History),
      (Circuit.seq first second).execute Reference state = state.mapClassical (fun entry =>
        ((bodyRecord entry.1).1, (entry.2, (bodyRecord entry.1).2))) := by
    intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord first second firstRecord rawRecord (by
      intro reference history historyFinite state
      refine (Circuit.execute_classical_mapClassical
        (widenedDenominatorOp (transport.liftInput denominator) widened) reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) rawEquation reference state
  let outerRecord := Circuit.workspaceRecord ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (Circuit.seq first second) bodyRecord
  have same := Circuit.executionRecord_unique (withWidenedXgcd denominator modulus outputs)
    record outerRecord equation (Circuit.execute_workspaceRecord _ _ _
      (Circuit.seq first second) bodyRecord bodyEquation)
  rw [same]
  let entered := store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh
  let enlarged := (firstRecord entered).1
  change [.classicalOperation (.wordResize width (width + 1))] ++
    (rawEngine input liftedOutputs).eventTrace (rawRecord enlarged).2 = _
  rw [xgcdNativeRawEngine_record_eventTrace input liftedOutputs liftedDistinct
    rawRecord rawEquation enlarged]
  have fresh : widened.key ∉ (transport.liftInput modulus).storageKeys := by
    rw [transport.liftInput_storageKeys]
    exact fun present => ctx.canonicalFreshKey_fresh (modulus.storageKeys_subset_context present)
  have enteredReads : transport.ReadsAs store entered :=
    (Transport.id ctx).workspaceTransport_readsAs_pushWorkspace _ _ _
      (Transport.workspaceTransport_readsAs_id store)
  have modulusRead : enlarged.read (transport.liftInput modulus) = store.read modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys entered
      (widenedDenominatorOp (transport.liftInput denominator) widened) _ fresh).trans
        (enteredReads modulus)
  have denominatorRead : enlarged.read (GCD.cellRead widened) =
      CShape.wordResize (width + 1) (store.read denominator) :=
    (Store.read_applyOp_output entered
      (widenedDenominatorOp (transport.liftInput denominator) widened)).trans
        (congrArg (CShape.wordResize (width + 1))
          (enteredReads denominator))
  have inputRead : enlarged.read input =
      .product (store.read modulus) (CShape.wordResize (width + 1) (store.read denominator)) :=
    congrArg₂ CShape.Value.product modulusRead denominatorRead
  rw [inputRead]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
