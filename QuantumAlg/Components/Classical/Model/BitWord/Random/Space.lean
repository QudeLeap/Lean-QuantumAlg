/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Exact live space of native random-bit generation

The output is an existing writable cell. The real unit-operand scope has a
single possible classical value and contributes zero bits at every scale.
All quantum systems and previously live classical cells remain present.
-/

namespace QuantumAlg.BitWord.Random

noncomputable section

private lemma unitSpace (kind : ProblemKind) :
    (SpacePool.ofShape .unit : SpacePool kind) = 0 := by
  funext axis
  cases kind <;> cases axis <;> rfl

variable {execution : ExecutionModel} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {width : Nat}

/-- The actual unit scope visits the original context, its one extension, and the original again.
-/
public lemma randomCode_visitedContexts (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    (code (execution := execution) output).visitedContexts path =
      [ctx, ctx.addWorkspace ctx.canonicalFreshKey .unit ctx.runtimeCtx_canonicalFreshKey_fresh,
        ctx] := by
  rfl

/-- Actual random generation adds no resident space at any classical or quantum coordinate. -/
public lemma randomCode_peakResidentSpace (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    (code (execution := execution) output).peakResidentSpace path = ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max
      (ctx.addWorkspace ctx.canonicalFreshKey .unit
        ctx.runtimeCtx_canonicalFreshKey_fresh).residentSpace
      (SpacePool.max ctx.residentSpace 0)) = ctx.residentSpace
  rw [RuntimeCtx.residentSpace_addWorkspace, unitSpace, zero_add,
    SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]

/-- The same actual unit scope adds no auxiliary bits or quantum systems. -/
public lemma randomCode_peakAuxiliarySpace (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    (code (execution := execution) output).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max
      (ctx.addWorkspace ctx.canonicalFreshKey .unit
        ctx.runtimeCtx_canonicalFreshKey_fresh).auxiliarySpace
      (SpacePool.max ctx.auxiliarySpace 0)) = ctx.auxiliarySpace
  rw [RuntimeCtx.auxiliarySpace_addWorkspace, unitSpace, zero_add,
    SpacePool.max_zero, SpacePool.max_self, SpacePool.max_self]

end

end QuantumAlg.BitWord.Random
