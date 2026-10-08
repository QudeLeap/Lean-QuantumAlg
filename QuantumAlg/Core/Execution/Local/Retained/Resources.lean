/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Context.Permutation.Local.Resources

/-!
# Actual local resources beside existing retained storage

Both existing compilers preserve every native event and evaluated dependency.
The retained head cell is physically present throughout each path and retains
its actual storage role. There is no new allocation instruction or allocation
charge; its complete native-dimensional resident and auxiliary space is counted.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  (code : Circuit model ctx ctx) (supported : code.IsLocal)
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

/-- The actual ordered native event trace is identical along corresponding execution paths. -/
theorem underRetained_eventTrace (path : code.Path) :
    (underRetained code supported key shape fresh).eventTrace
        (underRetainedPathEquiv code supported key shape fresh path) = code.eventTrace path :=
  (ContextPermutation.localCircuit_eventTrace (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh) (ctx.addRetained key shape fresh)
    (retainedLocalPermutation ctx key shape fresh)
    (ContextUnion.frameLocalPathEquiv code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh) path)).trans
    (ContextUnion.frameLocal_eventTrace code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh) path)

/-- Exact event multiplicities follow from the unchanged actual native trace. -/
theorem underRetained_resourcePool (path : code.Path) :
    (underRetained code supported key shape fresh).resourcePool
        (underRetainedPathEquiv code supported key shape fresh path) = code.resourcePool path :=
  congrArg ResourcePool.ofList (underRetained_eventTrace code supported key shape fresh path)

/-- Evaluated depth agrees for every assignment of native event durations. -/
theorem underRetained_depth (duration : Resource.Event model → Nat) (path : code.Path) :
    (underRetained code supported key shape fresh).depth duration
        (underRetainedPathEquiv code supported key shape fresh path) = code.depth duration path :=
  (ContextPermutation.localCircuit_depth (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh) (ctx.addRetained key shape fresh)
    (retainedLocalPermutation ctx key shape fresh) duration
    (ContextUnion.frameLocalPathEquiv code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh) path)).trans
    (ContextUnion.frameLocal_depth code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh) duration path)

/-- Every actual visited context is the same complete context with the existing retained cell. -/
theorem underRetained_visited (path : (underRetained code supported key shape fresh).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (underRetained code supported key shape fresh).visitedContexts path) :
    visited = ctx.addRetained key shape fresh :=
  ContextPermutation.localCircuit_visited (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh)
    (retainedLocalPermutation ctx key shape fresh) path visited present

/-- The resident peak counts the retained head and every original native-dimensional cell. -/
theorem underRetained_peakResidentSpace
    (path : (underRetained code supported key shape fresh).Path) :
    (underRetained code supported key shape fresh).peakResidentSpace path =
      SpacePool.ofShape shape + ctx.residentSpace :=
  (ContextPermutation.localCircuit_peakResidentSpace
    (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh)
    (retainedLocalPermutation ctx key shape fresh) path).trans
      (ContextPermutation.resident_space (retainedLocalPermutation ctx key shape fresh))

/-- The same retained storage role is counted in the exact auxiliary peak. -/
theorem underRetained_peakAuxiliarySpace
    (path : (underRetained code supported key shape fresh).Path) :
    (underRetained code supported key shape fresh).peakAuxiliarySpace path =
      SpacePool.ofShape shape + ctx.auxiliarySpace :=
  (ContextPermutation.localCircuit_peakAuxiliarySpace
    (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh)
    (retainedLocalPermutation ctx key shape fresh) path).trans
      (ContextPermutation.auxiliary_space (retainedLocalPermutation ctx key shape fresh))

end

end QuantumAlg.Circuit
