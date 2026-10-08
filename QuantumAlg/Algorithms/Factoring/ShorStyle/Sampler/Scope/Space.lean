/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Live peaks through the eleven actual sampler scopes

The allocation and release traces use the genuine parent contexts. Each is
bounded by the complete inner context; the body's full live peak is kept.
The composition adds no event and omits no intermediate storage stage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

private def ResidentBound {ctx : RuntimeCtx model.kind} (body : Circuit model ctx ctx)
    (path : body.Path) (budget : SpacePool model.kind) : Prop :=
  body.peakResidentSpace path ≤ budget

private theorem workspace_resident_le (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : body.Path) (budget : SpacePool model.kind) (parentBound : ctx.residentSpace ≤ budget)
    (bodyBound : ResidentBound body path budget) :
    ResidentBound (Circuit.workspace ctx key shape fresh body) path budget :=
  (Circuit.peakResidentSpace_workspace key shape fresh body path).le.trans
    (SpacePool.max_le parentBound bodyBound)

/-- Actual lexical entry and release retain the complete inner resident bound. -/
theorem samplerScopes_resident_le (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (path : body.Path) (budget : SpacePool model.kind)
    (contextBound : (Layout.context ctx width).residentSpace ≤ budget)
    (bodyBound : body.peakResidentSpace path ≤ budget) :
    (scopes ctx width body).peakResidentSpace path ≤ budget := by
  have stageBound (index : Fin 12) :
      ((Layout.stages ctx width).get
        ⟨index.val, by change index.val < 12; exact index.isLt⟩).residentSpace ≤ budget :=
    (Layout.samplerLayout_stage_resident_le ctx width _
      (List.get_mem (Layout.stages ctx width) _)).trans contextBound
  let stage10 := Circuit.workspace (Layout.availableCtx ctx width)
    (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh body
  have bound10 : ResidentBound stage10 path budget :=
    workspace_resident_le (Layout.availableCtx ctx width).canonicalFreshKey .bit
      (Layout.availableCtx ctx width).canonicalFreshKey_fresh body
      path budget (stageBound 10) bodyBound
  let stage9 := Circuit.workspace (Layout.selectedCtx ctx width)
    (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh stage10
  have bound9 : ResidentBound stage9 path budget :=
    workspace_resident_le (Layout.selectedCtx ctx width).canonicalFreshKey .bit
      (Layout.selectedCtx ctx width).canonicalFreshKey_fresh stage10
      path budget (stageBound 9) bound10
  let stage8 := Circuit.workspace (Layout.acceptedCtx ctx width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh stage9
  have bound8 : ResidentBound stage8 path budget :=
    workspace_resident_le (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh stage9
      path budget (stageBound 8) bound9
  let stage7 := Circuit.workspace (Layout.eligibleCtx ctx width)
    (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh stage8
  have bound7 : ResidentBound stage7 path budget :=
    workspace_resident_le (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
      (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh stage8
      path budget (stageBound 7) bound8
  let stage6 := Circuit.workspace (Layout.belowCtx ctx width)
    (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh stage7
  have bound6 : ResidentBound stage6 path budget :=
    workspace_resident_le (Layout.belowCtx ctx width).canonicalFreshKey .bit
      (Layout.belowCtx ctx width).canonicalFreshKey_fresh stage7 path budget (stageBound 6) bound7
  let stage5 := Circuit.workspace (Layout.positiveCtx ctx width)
    (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh stage6
  have bound5 : ResidentBound stage5 path budget :=
    workspace_resident_le (Layout.positiveCtx ctx width).canonicalFreshKey .bit
      (Layout.positiveCtx ctx width).canonicalFreshKey_fresh stage6
      path budget (stageBound 5) bound6
  let stage4 := Circuit.workspace (Layout.extendedCtx ctx width)
    (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh stage5
  have bound4 : ResidentBound stage4 path budget :=
    workspace_resident_le (Layout.extendedCtx ctx width).canonicalFreshKey .bit
      (Layout.extendedCtx ctx width).canonicalFreshKey_fresh stage5
      path budget (stageBound 4) bound5
  let stage3 := Circuit.workspace (Layout.candidateCtx ctx width)
    (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh stage4
  have bound3 : ResidentBound stage3 path budget :=
    workspace_resident_le (Layout.candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (Layout.candidateCtx ctx width).canonicalFreshKey_fresh stage4
      path budget (stageBound 3) bound4
  let stage2 := Circuit.workspace (Layout.gcdCtx ctx width)
    (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh stage3
  have bound2 : ResidentBound stage2 path budget :=
    workspace_resident_le (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.gcdCtx ctx width).canonicalFreshKey_fresh stage3 path budget (stageBound 2) bound3
  let stage1 := Circuit.workspace (Layout.modulusCtx ctx width)
    (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh stage2
  have bound1 : ResidentBound stage1 path budget :=
    workspace_resident_le (Layout.modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (Layout.modulusCtx ctx width).canonicalFreshKey_fresh stage2
      path budget (stageBound 1) bound2
  let stage0 := Circuit.workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh stage1
  have bound0 : ResidentBound stage0 path budget :=
    workspace_resident_le ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh stage1 path budget (stageBound 0) bound1
  exact bound0

private def AuxiliaryBound {ctx : RuntimeCtx model.kind} (body : Circuit model ctx ctx)
    (path : body.Path) (budget : SpacePool model.kind) : Prop :=
  body.peakAuxiliarySpace path ≤ budget

private theorem workspace_auxiliary_le (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : body.Path) (budget : SpacePool model.kind) (parentBound : ctx.auxiliarySpace ≤ budget)
    (bodyBound : AuxiliaryBound body path budget) :
    AuxiliaryBound (Circuit.workspace ctx key shape fresh body) path budget :=
  (Circuit.peakAuxiliarySpace_workspace key shape fresh body path).le.trans
    (SpacePool.max_le parentBound bodyBound)

/-- Actual lexical entry and release retain the complete inner auxiliary bound. -/
theorem samplerScopes_auxiliary_le (width : Nat)
    (body : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (path : body.Path) (budget : SpacePool model.kind)
    (contextBound : (Layout.context ctx width).auxiliarySpace ≤ budget)
    (bodyBound : body.peakAuxiliarySpace path ≤ budget) :
    (scopes ctx width body).peakAuxiliarySpace path ≤ budget := by
  have stageBound (index : Fin 12) :
      ((Layout.stages ctx width).get
        ⟨index.val, by change index.val < 12; exact index.isLt⟩).auxiliarySpace ≤ budget :=
    (Layout.samplerLayout_stage_auxiliary_le ctx width _
      (List.get_mem (Layout.stages ctx width) _)).trans contextBound
  let stage10 := Circuit.workspace (Layout.availableCtx ctx width)
    (Layout.availableCtx ctx width).canonicalFreshKey
    .bit (Layout.availableCtx ctx width).canonicalFreshKey_fresh body
  have bound10 : AuxiliaryBound stage10 path budget :=
    workspace_auxiliary_le (Layout.availableCtx ctx width).canonicalFreshKey .bit
      (Layout.availableCtx ctx width).canonicalFreshKey_fresh body
      path budget (stageBound 10) bodyBound
  let stage9 := Circuit.workspace (Layout.selectedCtx ctx width)
    (Layout.selectedCtx ctx width).canonicalFreshKey
    .bit (Layout.selectedCtx ctx width).canonicalFreshKey_fresh stage10
  have bound9 : AuxiliaryBound stage9 path budget :=
    workspace_auxiliary_le (Layout.selectedCtx ctx width).canonicalFreshKey .bit
      (Layout.selectedCtx ctx width).canonicalFreshKey_fresh stage10
      path budget (stageBound 9) bound10
  let stage8 := Circuit.workspace (Layout.acceptedCtx ctx width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh stage9
  have bound8 : AuxiliaryBound stage8 path budget :=
    workspace_auxiliary_le (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh stage9
      path budget (stageBound 8) bound9
  let stage7 := Circuit.workspace (Layout.eligibleCtx ctx width)
    (Layout.eligibleCtx ctx width).canonicalFreshKey
    .bit (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh stage8
  have bound7 : AuxiliaryBound stage7 path budget :=
    workspace_auxiliary_le (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
      (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh stage8
      path budget (stageBound 7) bound8
  let stage6 := Circuit.workspace (Layout.belowCtx ctx width)
    (Layout.belowCtx ctx width).canonicalFreshKey
    .bit (Layout.belowCtx ctx width).canonicalFreshKey_fresh stage7
  have bound6 : AuxiliaryBound stage6 path budget :=
    workspace_auxiliary_le (Layout.belowCtx ctx width).canonicalFreshKey .bit
      (Layout.belowCtx ctx width).canonicalFreshKey_fresh stage7 path budget (stageBound 6) bound7
  let stage5 := Circuit.workspace (Layout.positiveCtx ctx width)
    (Layout.positiveCtx ctx width).canonicalFreshKey
    .bit (Layout.positiveCtx ctx width).canonicalFreshKey_fresh stage6
  have bound5 : AuxiliaryBound stage5 path budget :=
    workspace_auxiliary_le (Layout.positiveCtx ctx width).canonicalFreshKey .bit
      (Layout.positiveCtx ctx width).canonicalFreshKey_fresh stage6
      path budget (stageBound 5) bound6
  let stage4 := Circuit.workspace (Layout.extendedCtx ctx width)
    (Layout.extendedCtx ctx width).canonicalFreshKey
    .bit (Layout.extendedCtx ctx width).canonicalFreshKey_fresh stage5
  have bound4 : AuxiliaryBound stage4 path budget :=
    workspace_auxiliary_le (Layout.extendedCtx ctx width).canonicalFreshKey .bit
      (Layout.extendedCtx ctx width).canonicalFreshKey_fresh stage5
      path budget (stageBound 4) bound5
  let stage3 := Circuit.workspace (Layout.candidateCtx ctx width)
    (Layout.candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.candidateCtx ctx width).canonicalFreshKey_fresh stage4
  have bound3 : AuxiliaryBound stage3 path budget :=
    workspace_auxiliary_le (Layout.candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (Layout.candidateCtx ctx width).canonicalFreshKey_fresh stage4
      path budget (stageBound 3) bound4
  let stage2 := Circuit.workspace (Layout.gcdCtx ctx width)
    (Layout.gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (Layout.gcdCtx ctx width).canonicalFreshKey_fresh stage3
  have bound2 : AuxiliaryBound stage2 path budget :=
    workspace_auxiliary_le (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.gcdCtx ctx width).canonicalFreshKey_fresh stage3 path budget (stageBound 2) bound3
  let stage1 := Circuit.workspace (Layout.modulusCtx ctx width)
    (Layout.modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (Layout.modulusCtx ctx width).canonicalFreshKey_fresh stage2
  have bound1 : AuxiliaryBound stage1 path budget :=
    workspace_auxiliary_le (Layout.modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (Layout.modulusCtx ctx width).canonicalFreshKey_fresh stage2
      path budget (stageBound 1) bound2
  let stage0 := Circuit.workspace ctx ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh stage1
  have bound0 : AuxiliaryBound stage0 path budget :=
    workspace_auxiliary_le ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh stage1 path budget (stageBound 0) bound1
  exact bound0

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
