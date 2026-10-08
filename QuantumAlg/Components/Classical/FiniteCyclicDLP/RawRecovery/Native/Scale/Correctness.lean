/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale.Placement

/-!
# Exact original frequency scaling through actual scratch scopes

The original raw and order words are read from their actual caller cells.
All scratch initialization and disjointness facts follow from the three
lexical allocations. Complete quantum-reference blocks are preserved by the
actual classical instructions, whose original widths and events are retained.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Placement

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Each actual lexical entry preserves all original structural source values. -/
theorem enterScale_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (enterScale store width).read (underScale input width) = store.read input := by
  unfold enterScale underScale
  rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace,
    Store.read_pushWorkspace_underWorkspace]

/-- Each matching lexical release exposes the unchanged old structural reference. -/
theorem leaveScale_read (store : Store (scaleCtx ctx width)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (leaveScale store).read input = store.read (underScale input width) := by
  unfold leaveScale underScale
  rw [Store.read_popWorkspace_underWorkspace, Store.read_popWorkspace_underWorkspace,
    Store.read_popWorkspace_underWorkspace]

/-- The denominator's actual allocation supplies exactly the loader's zero initial value. -/
theorem enterScale_denominator_zero (store : Store ctx) (width : Nat) :
    ((enterScale store width).read (scaleRead (scaleDenominatorCell ctx width))).toNat = 0 := by
  unfold enterScale scaleDenominatorCell scaleRead
  change ((((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).pushWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).pushWorkspace
        (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh).read
    (((CInputRef.storage (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey
      (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh)).underWorkspace
      (scaleDenominatorCtx ctx width).canonicalFreshKey (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).underWorkspace
      (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
      (scaleProductCtx ctx width).canonicalFreshKey_fresh)).toNat = 0
  rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace,
    Store.read_pushWorkspace_head]
  rfl

private theorem scaleDenominator_free {shape : CShape} (input : CInputRef ctx shape) :
    (scaleDenominatorCell ctx width).key ∉ (underScale input width).storageKeys := by
  change ctx.canonicalFreshKey ∉ (underScale input width).storageKeys
  simp only [underScale, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

private theorem scaleProduct_denominator_separate :
    (scaleProductCell ctx width).key ∉
      (scaleRead (scaleDenominatorCell ctx width)).storageKeys := by
  change (scaleDenominatorCtx ctx width).canonicalFreshKey ∉ [ctx.canonicalFreshKey]
  intro present
  apply (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
  rw [List.mem_singleton.mp present]
  exact List.mem_cons_self

end Placement

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The real loader and arithmetic compose on the complete service-aware execution state. -/
theorem scalePrepared_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (scaleCtx ctx width) Reference (model.HiddenState × History)) :
    (scalePrepared (model := model) raw modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalePreparedStep (model := model) raw modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (scaleSeed (model := model) (scaleDenominatorCell ctx width))
    (scalePlaced (model := model) raw modulus output)
    (fun before =>
      let result := scaleSeedStep (model := model) (scaleDenominatorCell ctx width) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := scaleStep (model := model) (underScale raw width) (underScale modulus width)
        (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
        (scaleDivisionCell ctx width) (writeUnderScale output width) before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (scaleSeed_execute (model := model) (scaleDenominatorCell ctx width)
      reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (scaleBody_execute (model := model) (underScale raw width) (underScale modulus width)
      (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
      (scaleDivisionCell ctx width) (writeUnderScale output width) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

private def divisionScope (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (scaleProductCtx ctx width) (scaleProductCtx ctx width) :=
  .workspace (scaleProductCtx ctx width) (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
    (scalePrepared (model := model) raw modulus output)

private def divisionScopeStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleProductCtx ctx width)) :
    Store (scaleProductCtx ctx width) × (divisionScope (model := model) raw modulus output).Path :=
  let result := scalePreparedStep (model := model) raw modulus output
    (store.pushWorkspace (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
      (scaleProductCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
    (scaleProductCtx ctx width).canonicalFreshKey_fresh result.1, result.2)

private theorem divisionScope_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (scaleProductCtx ctx width) Reference (model.HiddenState × History)) :
    (divisionScope (model := model) raw modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := divisionScopeStep (model := model) raw modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
    (scalePrepared (model := model) raw modulus output)
    (fun before =>
      let result := scalePreparedStep (model := model) raw modulus output before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (scalePrepared_execute (model := model) raw modulus output reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

private def productScope (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width) :=
  .workspace (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    (divisionScope (model := model) raw modulus output)

private def productScopeStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleDenominatorCtx ctx width)) :
    Store (scaleDenominatorCtx ctx width) ×
      (productScope (model := model) raw modulus output).Path :=
  let result := divisionScopeStep (model := model) raw modulus output
    (store.pushWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    result.1, result.2)

private theorem productScope_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (scaleDenominatorCtx ctx width) Reference (model.HiddenState × History)) :
    (productScope (model := model) raw modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := productScopeStep (model := model) raw modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    (divisionScope (model := model) raw modulus output)
    (fun before =>
      let result := divisionScopeStep (model := model) raw modulus output before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (divisionScope_execute (model := model) raw modulus output reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete actual three-scope circuit preserves all quantum-reference blocks and paths. -/
theorem withScale_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (withScale (model := model) raw modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := withScaleStep (model := model) raw modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (productScope (model := model) raw modulus output)
    (fun before =>
      let result := productScopeStep (model := model) raw modulus output before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (productScope_execute (model := model) raw modulus output reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete actual scale writes the original model's exact canonical rescaled frequency. -/
theorem withScale_original_value (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus) :
    ((withScaleStep (model := model) raw modulus output store).1.read (scaleRead output)).toNat =
      (scaleFrequency spec (store.read raw).toNat).val := by
  let entered := enterScale store width
  let seeded := (scaleSeedStep (model := model) (scaleDenominatorCell ctx width) entered).1
  have originalRaw : seeded.read (underScale raw width) = store.read raw :=
    (scaleSeed_read_other (scaleDenominatorCell ctx width) entered (underScale raw width)
      (scaleDenominator_free raw)).trans (enterScale_read store raw width)
  have originalOrder : seeded.read (underScale modulus width) = store.read modulus :=
    (scaleSeed_read_other (scaleDenominatorCell ctx width) entered (underScale modulus width)
      (scaleDenominator_free modulus)).trans (enterScale_read store modulus width)
  have denominator := scaleSeed_zero_value (model := model) (scaleDenominatorCell ctx width) entered
    (enterScale_denominator_zero store width)
  have written := scaleBody_result (underScale raw width) (underScale modulus width)
    (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
    (scaleDivisionCell ctx width) (writeUnderScale output width)
    scaleProduct_denominator_separate seeded
  have value := scaleWordValue_original spec (seeded.read (underScale raw width))
    (seeded.read (underScale modulus width))
    (seeded.read (scaleRead (scaleDenominatorCell ctx width)))
    ((congrArg CShape.Value.toNat originalOrder).trans orderValue) denominator
  have exitRead := leaveScale_read
    (scalePreparedStep (model := model) raw modulus output entered).1 (scaleRead output)
  exact (congrArg CShape.Value.toNat exitRead).trans
    ((congrArg CShape.Value.toNat written).trans
      (value.trans (congrArg (fun operand => (scaleFrequency spec operand.toNat).val) originalRaw)))

/-- Independent original denominator-loader and exact full-width arithmetic coordinates. -/
def scaleEvents (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1)))] ++
    Word.PowerOfTwo.shiftTrace (model := model) (width + 1) width ++
      scaleBodyEvents (model := model) width

/-- Actual allocations and releases surround precisely the original charged native sequence. -/
theorem withScale_eventTrace (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).eventTrace path =
      scaleEvents (model := model) width := by
  change ((BitWord.instruction (execution := model)
    (Word.PowerOfTwo.incrementOp (scaleDenominatorCell ctx width))).eventTrace path.1.1 ++
    (Word.PowerOfTwo.shiftInto (model := model) width (scaleDenominatorCell ctx width)).eventTrace
      path.1.2) ++ (scalePlaced (model := model) raw modulus output).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, Word.PowerOfTwo.shiftInto_events]
  exact congrArg (fun trace =>
    [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1)))] ++
      Word.PowerOfTwo.shiftTrace (model := model) (width + 1) width ++ trace)
    (scaleBody_eventTrace (model := model) (underScale raw width) (underScale modulus width)
      (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
      (scaleDivisionCell ctx width) (writeUnderScale output width) path.2)

/-- Native multiplicities derive from the same original loader and arithmetic instructions. -/
theorem withScale_resourcePool (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).resourcePool path =
      ResourcePool.ofList (scaleEvents (model := model) width) :=
  congrArg ResourcePool.ofList (withScale_eventTrace raw modulus output path)

/-- Exact serial unit-duration depth includes every denominator-loader and arithmetic event. -/
theorem withScale_depth (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withScale (model := model) raw modulus output).Path) :
    (withScale (model := model) raw modulus output).depth (fun _ => 1) path = width + 4 := by
  change (1 + (Word.PowerOfTwo.shiftInto (model := model) width
    (scaleDenominatorCell ctx width)).depth (fun _ => 1) path.1.2) + 3 = _
  rw [Word.PowerOfTwo.shiftInto_depth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
