/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Resources
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent budgets for native sampling and allocated classical recovery

The budgets combine one actual native batch with the full classical recovery.
Space retains the original bank and all sampled results, the new optional
factor, all eight recovery packages, and the native modular-power workspace.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

open Execution
open ShortDLP.CompiledMAU

noncomputable section

-- The original bank is already constructed; only its proved capacity is needed here.
attribute [local irreducible] NativeBatchReuse.context

/-- Independent native multiplicities include the later sampled batch and full recovery. -/
def eventEnvelope (N : Nat) : ResourcePool RuntimeRound.model :=
  NativeBatchReuse.nativeEnvelope N +
    LatticeFixedBatchRecoveryMachine.eventEnvelope (model := RuntimeRound.model) N

/-- Independent sequential depth includes the dependence from sampling through final recovery. -/
def depthBound (N : Nat) : Nat :=
  NativeBatchReuse.unitDepthBound N + LatticeFixedBatchRecoveryMachine.depthBound N

/-- Recovery retains one factor and temporarily allocates the complete classical workspace. -/
def tailAdditionalSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N

/-- One bank, every retained result and the full classical recovery fit this parameter budget. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  NativeBatchReuse.additionalSpace N + tailAdditionalSpace N

private lemma sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit RuntimeRound.model pre middle)
    (second : Circuit RuntimeRound.model middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

private lemma retained_pool_le (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit RuntimeRound.model
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (budget : ResourcePool RuntimeRound.model)
    (bounded : ∀ path, inner.resourcePool path ≤ budget)
    (path : (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).Path) :
    (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).resourcePool
        path ≤ budget :=
  bounded path.2

private lemma retained_depth_le (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit RuntimeRound.model
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (budget : Nat) (bounded : ∀ path, inner.depth (fun _ => 1) path ≤ budget)
    (path : (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).Path) :
    (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).depth
        (fun _ => 1) path ≤ budget := by
  change 0 + inner.depth (fun _ => 1) path.2 ≤ budget
  exact (Nat.zero_add _).le.trans (bounded path.2)

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (ShortDLP.CompiledMAU.runtimeLayout
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

private lemma context_residentSpace (N : Nat) :
    (context base N).residentSpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatchReuse.context base N).residentSpace :=
  RuntimeCtx.residentSpace_addRetained (NativeBatchReuse.context base N)
    (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

private lemma context_auxiliarySpace (N : Nat) :
    (context base N).auxiliarySpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatchReuse.context base N).auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addRetained (NativeBatchReuse.context base N)
    (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- Real retained allocation emits no event, and the full body obeys its independent budget. -/
lemma tail_pool_le (input : Input N) (path : (tail base input).Path) :
    (tail base input).resourcePool path ≤
      LatticeFixedBatchRecoveryMachine.eventEnvelope (model := RuntimeRound.model) N := by
  unfold tail at path ⊢
  apply retained_pool_le
  intro selected
  unfold body at selected ⊢
  exact LatticeFixedBatchRecoveryMachine.into_pool_le
    (model := RuntimeRound.model) input (sourceParameter base N)
    (terminals base N) (resultRef base N) selected

/-- Retained allocation adds no event duration to the actual complete recovery dependence. -/
lemma tail_depth_le (input : Input N) (path : (tail base input).Path) :
    (tail base input).depth (fun _ => 1) path ≤
      LatticeFixedBatchRecoveryMachine.depthBound N := by
  unfold tail at path ⊢
  apply retained_depth_le
  intro selected
  unfold body at selected ⊢
  exact LatticeFixedBatchRecoveryMachine.into_depth_le
    (model := RuntimeRound.model) input
    (sourceParameter base N) (terminals base N)
    (resultRef base N) selected

/-- Every complete execution path satisfies the independent native-coordinate allowance. -/
lemma code_pool_le (input : Input N) (path : (code base sameWires originalCells input).Path) :
    (code base sameWires originalCells input).resourcePool path ≤ eventEnvelope N :=
  (sequence_pool (NativeBatchReuse.code base N sameWires originalCells)
    (tail base input) path).le.trans
    (add_le_add (NativeBatchReuse.nativeBatchReuse_resourcePool_le
      base N sameWires originalCells path.1)
      (tail_pool_le base input path.2))

/-- The same independent event ledger bounds the number of emitted operations. -/
lemma code_eventCount_le (input : Input N)
    (path : (code base sameWires originalCells input).Path) :
    ((code base sameWires originalCells input).eventTrace path).length ≤
      (eventEnvelope N).card :=
  Multiset.card_le_card (code_pool_le base sameWires originalCells input path)

/-- The complete actual sequential path obeys the independent unit-duration depth formula. -/
lemma code_depth_le (input : Input N) (path : (code base sameWires originalCells input).Path) :
    (code base sameWires originalCells input).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add (NativeBatchReuse.nativeBatchReuse_unitDepth_le
    base N sameWires originalCells path.1)
    (tail_depth_le base input path.2)

private lemma nativeContext_resident_le (N : Nat) :
    (NativeBatchReuse.context base N).residentSpace ≤
      base.residentSpace + NativeBatchReuse.additionalSpace N := by
  have actual := RuntimeResults.shortDLP_runtimeResults_resident
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledContext base N) 16
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident base N
  rw [NativeBatchReuse.context, actual, NativeBatchReuse.sampledContext, sampled]
  change 16 • SpacePool.ofShape (.bits (measurementBits N)) +
    (base.residentSpace +
      ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N)) ≤ _
  intro axis
  cases axis <;>
    simp [NativeBatchReuse.additionalSpace,
      ShorStyle.Canonical.Sampler.Retained.resultSpace, SpacePool.ofShape]
  omega

private lemma nativeContext_auxiliary_le (N : Nat) :
    (NativeBatchReuse.context base N).auxiliarySpace ≤
      base.auxiliarySpace + NativeBatchReuse.additionalSpace N := by
  have actual := RuntimeResults.shortDLP_runtimeResults_auxiliary
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledContext base N) 16
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary base N
  rw [NativeBatchReuse.context, actual, NativeBatchReuse.sampledContext, sampled]
  change 16 • SpacePool.ofShape (.bits (measurementBits N)) +
    (base.auxiliarySpace +
      ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N)) ≤ _
  intro axis
  cases axis <;>
    simp [NativeBatchReuse.additionalSpace,
      ShorStyle.Canonical.Sampler.Retained.resultSpace, SpacePool.ofShape]
  omega

/-- Every tail context includes the same source bank plus the full classical live allowance. -/
lemma tail_resident_le (input : Input N) (path : (tail base input).Path) :
    (tail base input).peakResidentSpace path ≤
      (NativeBatchReuse.context base N).residentSpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max ((NativeBatchReuse.context base N).residentSpace axis)
      (max ((context base N).residentSpace axis) 0) ≤ _
    rw [context_residentSpace]
    change max _ (max (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis + _) 0)
      ≤ (NativeBatchReuse.context base N).residentSpace axis +
        (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
          LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    omega
  · unfold body at path ⊢
    have bound := LatticeFixedBatchRecoveryMachine.into_resident_le
      (model := RuntimeRound.model) input
      (sourceParameter base N) (terminals base N)
      (resultRef base N) path.2
    intro axis
    have actual := bound axis
    rw [context_residentSpace] at actual
    change _ ≤ (NativeBatchReuse.context base N).residentSpace axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    change _ ≤ LatticeFixedBatchRecoveryMachine.additionalSpace
      (model := RuntimeRound.model) N axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        (NativeBatchReuse.context base N).residentSpace axis) at actual
    omega

/-- Auxiliary roles retain all source entries while charging every allocated recovery cell. -/
lemma tail_auxiliary_le (input : Input N) (path : (tail base input).Path) :
    (tail base input).peakAuxiliarySpace path ≤
      (NativeBatchReuse.context base N).auxiliarySpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max ((NativeBatchReuse.context base N).auxiliarySpace axis)
      (max ((context base N).auxiliarySpace axis) 0) ≤ _
    rw [context_auxiliarySpace]
    change max _ (max (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis + _) 0)
      ≤ (NativeBatchReuse.context base N).auxiliarySpace axis +
        (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
          LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    omega
  · unfold body at path ⊢
    have bound := LatticeFixedBatchRecoveryMachine.into_auxiliary_le
      (model := RuntimeRound.model) input
      (sourceParameter base N) (terminals base N)
      (resultRef base N) path.2
    intro axis
    have actual := bound axis
    rw [context_auxiliarySpace] at actual
    change _ ≤ (NativeBatchReuse.context base N).auxiliarySpace axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    change _ ≤ LatticeFixedBatchRecoveryMachine.additionalSpace
      (model := RuntimeRound.model) N axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        (NativeBatchReuse.context base N).auxiliarySpace axis) at actual
    omega

/-- Full resident accounting includes one bank, every retained result and all recovery scratch. -/
lemma code_resident_le (input : Input N) (path : (code base sameWires originalCells input).Path) :
    (code base sameWires originalCells input).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N := by
  unfold code at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · intro axis
    have bound := NativeBatchReuse.nativeBatchReuse_resident_le
      base N sameWires originalCells path.1 axis
    change _ ≤ base.residentSpace axis +
      (NativeBatchReuse.additionalSpace N axis + tailAdditionalSpace N axis)
    change _ ≤ base.residentSpace axis + NativeBatchReuse.additionalSpace N axis at bound
    omega
  · have tailBound := tail_resident_le base input path.2
    have nativeBound := nativeContext_resident_le base N
    intro axis
    exact (tailBound axis).trans ((Nat.add_le_add_right (nativeBound axis) _).trans_eq
      (Nat.add_assoc _ _ _))

/-- Full auxiliary accounting uses the same real bank and retained cells at every actual peak. -/
lemma code_auxiliary_le (input : Input N)
    (path : (code base sameWires originalCells input).Path) :
    (code base sameWires originalCells input).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N := by
  unfold code at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · intro axis
    have bound := NativeBatchReuse.nativeBatchReuse_auxiliary_le
      base N sameWires originalCells path.1 axis
    change _ ≤ base.auxiliarySpace axis +
      (NativeBatchReuse.additionalSpace N axis + tailAdditionalSpace N axis)
    change _ ≤ base.auxiliarySpace axis + NativeBatchReuse.additionalSpace N axis at bound
    omega
  · have tailBound := tail_auxiliary_le base input path.2
    have nativeBound := nativeContext_auxiliary_le base N
    intro axis
    exact (tailBound axis).trans ((Nat.add_le_add_right (nativeBound axis) _).trans_eq
      (Nat.add_assoc _ _ _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
