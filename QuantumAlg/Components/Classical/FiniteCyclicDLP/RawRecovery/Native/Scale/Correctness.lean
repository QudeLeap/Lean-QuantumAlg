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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The real loader and full-width arithmetic compose on the same complete execution state. -/
theorem scalePrepared_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (scaleCtx ctx width) Reference History) :
    (scalePrepared raw modulus output).execute Reference state = state.mapClassical (fun entry =>
      ((scalePreparedStep raw modulus output entry.1).1,
        (entry.2, (scalePreparedStep raw modulus output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (scaleSeed (scaleDenominatorCell ctx width))
    (scalePlaced raw modulus output) (scaleSeedStep (scaleDenominatorCell ctx width))
    (fun store => (scaleStore (underScale raw width) (underScale modulus width)
      (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
      (scaleDivisionCell ctx width) (writeUnderScale output width) store, ((), ((), ()))))
    (scaleSeed_execute (scaleDenominatorCell ctx width)) (by
      intro reference history _ initial
      refine (scaleBody_execute (underScale raw width) (underScale modulus width)
        (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
        (scaleDivisionCell ctx width) (writeUnderScale output width) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private def divisionScope (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (scaleProductCtx ctx width) (scaleProductCtx ctx width) :=
  .workspace (scaleProductCtx ctx width) (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
    (scalePrepared raw modulus output)

private def divisionScopeStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleProductCtx ctx width)) :
    Store (scaleProductCtx ctx width) × (divisionScope raw modulus output).Path :=
  let result := scalePreparedStep raw modulus output
    (store.pushWorkspace (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
      (scaleProductCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
    (scaleProductCtx ctx width).canonicalFreshKey_fresh result.1, result.2)

private theorem divisionScope_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (scaleProductCtx ctx width) Reference History) :
    (divisionScope raw modulus output).execute Reference state = state.mapClassical (fun entry =>
      ((divisionScopeStep raw modulus output entry.1).1,
        (entry.2, (divisionScopeStep raw modulus output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
    (scalePrepared raw modulus output) (scalePreparedStep raw modulus output)
    (scalePrepared_execute raw modulus output) Reference state).trans ?_
  congr 1

private def productScope (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width) :=
  .workspace (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    (divisionScope raw modulus output)

private def productScopeStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleDenominatorCtx ctx width)) :
    Store (scaleDenominatorCtx ctx width) × (productScope raw modulus output).Path :=
  let result := divisionScopeStep raw modulus output
    (store.pushWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    result.1, result.2)

private theorem productScope_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (scaleDenominatorCtx ctx width) Reference History) :
    (productScope raw modulus output).execute Reference state = state.mapClassical (fun entry =>
      ((productScopeStep raw modulus output entry.1).1,
        (entry.2, (productScopeStep raw modulus output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
    (divisionScope raw modulus output) (divisionScopeStep raw modulus output)
    (divisionScope_execute raw modulus output) Reference state).trans ?_
  congr 1

/-- The complete actual three-scope circuit preserves all quantum-reference blocks and paths. -/
theorem withScale_execute (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (withScale raw modulus output).execute Reference state = state.mapClassical (fun entry =>
      ((withScaleStep raw modulus output entry.1).1,
        (entry.2, (withScaleStep raw modulus output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (productScope raw modulus output) (productScopeStep raw modulus output)
    (productScope_execute raw modulus output) Reference state).trans ?_
  congr 1

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

/-- The complete actual scale writes the original model's exact canonical rescaled frequency. -/
theorem withScale_original_value (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (orderValue : (store.read modulus).toNat = spec.modulus) :
    ((withScaleStep raw modulus output store).1.read (scaleRead output)).toNat =
      (scaleFrequency spec (store.read raw).toNat).val := by
  let entered := enterScale store width
  let seeded := (scaleSeedStep (scaleDenominatorCell ctx width) entered).1
  have originalRaw : seeded.read (underScale raw width) = store.read raw :=
    (scaleSeed_read_other (scaleDenominatorCell ctx width) entered (underScale raw width)
      (scaleDenominator_free raw)).trans (enterScale_read store raw width)
  have originalOrder : seeded.read (underScale modulus width) = store.read modulus :=
    (scaleSeed_read_other (scaleDenominatorCell ctx width) entered (underScale modulus width)
      (scaleDenominator_free modulus)).trans (enterScale_read store modulus width)
  have denominator := scaleSeed_zero_value (scaleDenominatorCell ctx width) entered
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
    (scalePreparedStep raw modulus output entered).1 (scaleRead output)
  exact (congrArg CShape.Value.toNat exitRead).trans
    ((congrArg CShape.Value.toNat written).trans
      (value.trans (congrArg (fun operand => (scaleFrequency spec operand.toNat).val) originalRaw)))

/-- Independent original denominator-loader and exact full-width arithmetic coordinates. -/
def scaleEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .increment (width + 1))] ++
    Word.PowerOfTwo.shiftTrace (width + 1) width ++ scaleBodyEvents kind width

/-- Actual allocations and releases surround precisely the original charged native sequence. -/
theorem withScale_eventTrace (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withScale raw modulus output).Path) :
    (withScale raw modulus output).eventTrace path = scaleEvents kind width := by
  change (_ ++ (Word.PowerOfTwo.shiftInto width (scaleDenominatorCell ctx width)).eventTrace
    path.1.2) ++ (scalePlaced raw modulus output).eventTrace path.2 = _
  rw [Word.PowerOfTwo.shiftInto_events]
  rfl

/-- Native multiplicities derive from the same original loader and arithmetic instructions. -/
theorem withScale_resourcePool (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withScale raw modulus output).Path) :
    (withScale raw modulus output).resourcePool path =
      ResourcePool.ofList (scaleEvents kind width) :=
  congrArg ResourcePool.ofList (withScale_eventTrace raw modulus output path)

/-- Exact serial unit-duration depth includes every denominator-loader and arithmetic event. -/
theorem withScale_depth (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withScale raw modulus output).Path) :
    (withScale raw modulus output).depth (fun _ => 1) path = width + 4 := by
  change (1 + (Word.PowerOfTwo.shiftInto width (scaleDenominatorCell ctx width)).depth
    (fun _ => 1) path.1.2) + 3 = _
  rw [Word.PowerOfTwo.shiftInto_depth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
