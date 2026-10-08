/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Space
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent budgets for native sampling and allocated classical recovery

The budgets combine one actual native batch with the full classical recovery.
Space retains the original bank and all sampled results, the new optional
factor, all eight recovery packages, and the native modular-power workspace.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

open Execution
open ShortDLP.CompiledMAU

noncomputable section

-- The original bank is already constructed; only its proved capacity is needed here.
attribute [local irreducible] NativeBatch.context

/-- Independent native multiplicities include the original first batch and full recovery. -/
def eventEnvelope (N : Nat) : ResourcePool RuntimeRound.model :=
  NativeBatch.nativeEnvelope N +
    LatticeFixedBatchRecoveryMachine.eventEnvelope (model := RuntimeRound.model) N

/-- Independent sequential depth includes the dependence from sampling through final recovery. -/
def depthBound (N : Nat) : Nat :=
  NativeBatch.unitDepthBound N + LatticeFixedBatchRecoveryMachine.depthBound N

/-- Recovery retains one factor and temporarily allocates the complete classical workspace. -/
def tailAdditionalSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N

/-- One bank, every retained result and the full classical recovery fit this parameter budget. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  NativeBatch.additionalSpace N + tailAdditionalSpace N

private theorem sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit RuntimeRound.model pre middle)
    (second : Circuit RuntimeRound.model middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

private theorem retained_pool_le (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit RuntimeRound.model
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (budget : ResourcePool RuntimeRound.model)
    (bounded : ∀ path, inner.resourcePool path ≤ budget)
    (path : (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).Path) :
    (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).resourcePool
        path ≤ budget :=
  bounded path.2

private theorem retained_depth_le (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys)
    (inner : Circuit RuntimeRound.model
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (budget : Nat) (bounded : ∀ path, inner.depth (fun _ => 1) path ≤ budget)
    (path : (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).Path) :
    (Circuit.seq (.retain (model := RuntimeRound.model) ctx key shape fresh) inner).depth
        (fun _ => 1) path ≤ budget := by
  change 0 + inner.depth (fun _ => 1) path.2 ≤ budget
  exact (Nat.zero_add _).le.trans (bounded path.2)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

private theorem context_residentSpace (N : Nat) :
    (context base noQuantum N).residentSpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatch.context base noQuantum N).residentSpace :=
  RuntimeCtx.residentSpace_addRetained (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

private theorem context_auxiliarySpace (N : Nat) :
    (context base noQuantum N).auxiliarySpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatch.context base noQuantum N).auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addRetained (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- Real retained allocation emits no event, and the full body obeys its independent budget. -/
theorem tail_pool_le (input : Input N) (path : (tail base noQuantum input).Path) :
    (tail base noQuantum input).resourcePool path ≤
      LatticeFixedBatchRecoveryMachine.eventEnvelope (model := RuntimeRound.model) N := by
  unfold tail at path ⊢
  apply retained_pool_le
  intro selected
  unfold body at selected ⊢
  exact LatticeFixedBatchRecoveryMachine.into_pool_le
    (model := RuntimeRound.model) input (sourceParameter base noQuantum N)
    (terminals base noQuantum N) (resultRef base noQuantum N) selected

/-- Retained allocation adds no event duration to the actual complete recovery dependence. -/
theorem tail_depth_le (input : Input N) (path : (tail base noQuantum input).Path) :
    (tail base noQuantum input).depth (fun _ => 1) path ≤
      LatticeFixedBatchRecoveryMachine.depthBound N := by
  unfold tail at path ⊢
  apply retained_depth_le
  intro selected
  unfold body at selected ⊢
  exact LatticeFixedBatchRecoveryMachine.into_depth_le
    (model := RuntimeRound.model) input
    (sourceParameter base noQuantum N) (terminals base noQuantum N)
    (resultRef base noQuantum N) selected

/-- Every complete execution path satisfies the independent native-coordinate allowance. -/
theorem code_pool_le (input : Input N) (path : (code base noQuantum input).Path) :
    (code base noQuantum input).resourcePool path ≤ eventEnvelope N :=
  (sequence_pool (NativeBatch.code base noQuantum N) (tail base noQuantum input) path).le.trans
    (add_le_add (NativeBatch.nativeBatch_resourcePool_le base noQuantum N path.1)
      (tail_pool_le base noQuantum input path.2))

/-- The complete actual sequential path obeys the independent unit-duration depth formula. -/
theorem code_depth_le (input : Input N) (path : (code base noQuantum input).Path) :
    (code base noQuantum input).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add (NativeBatch.nativeBatch_unitDepth_le base noQuantum N path.1)
    (tail_depth_le base noQuantum input path.2)

private theorem nativeContext_resident_le (N : Nat) :
    (NativeBatch.context base noQuantum N).residentSpace ≤
      base.residentSpace + NativeBatch.additionalSpace N := by
  have actual := RuntimeResults.shortDLP_runtimeResults_resident
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.readyContext base noQuantum N) 16
  have budget := NativeBatch.nativeBatch_rounds_resident_budget base noQuantum N
  rw [NativeBatch.context, actual]
  intro axis
  have bound := budget axis
  change (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
    (NativeBatch.readyContext base noQuantum N).residentSpace axis ≤ _
  change SpacePool.ofShape (.finite 2) axis +
    (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
    (NativeBatch.readyContext base noQuantum N).residentSpace axis ≤ _ at bound
  omega

private theorem nativeContext_auxiliary_le (N : Nat) :
    (NativeBatch.context base noQuantum N).auxiliarySpace ≤
      base.auxiliarySpace + NativeBatch.additionalSpace N := by
  have actual := RuntimeResults.shortDLP_runtimeResults_auxiliary
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.readyContext base noQuantum N) 16
  have budget := NativeBatch.nativeBatch_rounds_auxiliary_budget base noQuantum N
  rw [NativeBatch.context, actual]
  intro axis
  have bound := budget axis
  change (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
    (NativeBatch.readyContext base noQuantum N).auxiliarySpace axis ≤ _
  change SpacePool.ofShape (.finite 2) axis +
    (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
    (NativeBatch.readyContext base noQuantum N).auxiliarySpace axis ≤ _ at bound
  omega

/-- Every tail context includes the same source bank plus the full classical live allowance. -/
theorem tail_resident_le (input : Input N) (path : (tail base noQuantum input).Path) :
    (tail base noQuantum input).peakResidentSpace path ≤
      (NativeBatch.context base noQuantum N).residentSpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max ((NativeBatch.context base noQuantum N).residentSpace axis)
      (max ((context base noQuantum N).residentSpace axis) 0) ≤ _
    rw [context_residentSpace]
    change max _ (max (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis + _) 0)
      ≤ (NativeBatch.context base noQuantum N).residentSpace axis +
        (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
          LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    omega
  · unfold body at path ⊢
    have bound := LatticeFixedBatchRecoveryMachine.into_resident_le
      (model := RuntimeRound.model) input
      (sourceParameter base noQuantum N) (terminals base noQuantum N)
      (resultRef base noQuantum N) path.2
    intro axis
    have actual := bound axis
    rw [context_residentSpace] at actual
    change _ ≤ (NativeBatch.context base noQuantum N).residentSpace axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    change _ ≤ LatticeFixedBatchRecoveryMachine.additionalSpace
      (model := RuntimeRound.model) N axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        (NativeBatch.context base noQuantum N).residentSpace axis) at actual
    omega

/-- Auxiliary roles retain all source entries while charging every allocated recovery cell. -/
theorem tail_auxiliary_le (input : Input N) (path : (tail base noQuantum input).Path) :
    (tail base noQuantum input).peakAuxiliarySpace path ≤
      (NativeBatch.context base noQuantum N).auxiliarySpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max ((NativeBatch.context base noQuantum N).auxiliarySpace axis)
      (max ((context base noQuantum N).auxiliarySpace axis) 0) ≤ _
    rw [context_auxiliarySpace]
    change max _ (max (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis + _) 0)
      ≤ (NativeBatch.context base noQuantum N).auxiliarySpace axis +
        (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
          LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    omega
  · unfold body at path ⊢
    have bound := LatticeFixedBatchRecoveryMachine.into_auxiliary_le
      (model := RuntimeRound.model) input
      (sourceParameter base noQuantum N) (terminals base noQuantum N)
      (resultRef base noQuantum N) path.2
    intro axis
    have actual := bound axis
    rw [context_auxiliarySpace] at actual
    change _ ≤ (NativeBatch.context base noQuantum N).auxiliarySpace axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        LatticeFixedBatchRecoveryMachine.additionalSpace (model := RuntimeRound.model) N axis)
    change _ ≤ LatticeFixedBatchRecoveryMachine.additionalSpace
      (model := RuntimeRound.model) N axis +
      (SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) axis +
        (NativeBatch.context base noQuantum N).auxiliarySpace axis) at actual
    omega

/-- Full resident accounting includes one bank, every retained result and all recovery scratch. -/
theorem code_resident_le (input : Input N) (path : (code base noQuantum input).Path) :
    (code base noQuantum input).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N := by
  unfold code at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · intro axis
    have bound := NativeBatch.nativeBatch_peakResidentSpace_le base noQuantum N path.1 axis
    change _ ≤ base.residentSpace axis +
      (NativeBatch.additionalSpace N axis + tailAdditionalSpace N axis)
    change _ ≤ base.residentSpace axis + NativeBatch.additionalSpace N axis at bound
    omega
  · have tailBound := tail_resident_le base noQuantum input path.2
    have nativeBound := nativeContext_resident_le base noQuantum N
    intro axis
    exact (tailBound axis).trans ((Nat.add_le_add_right (nativeBound axis) _).trans_eq
      (Nat.add_assoc _ _ _))

/-- Full auxiliary accounting uses the same real bank and retained cells at every actual peak. -/
theorem code_auxiliary_le (input : Input N) (path : (code base noQuantum input).Path) :
    (code base noQuantum input).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N := by
  unfold code at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · intro axis
    have bound := NativeBatch.nativeBatch_peakAuxiliarySpace_le base noQuantum N path.1 axis
    change _ ≤ base.auxiliarySpace axis +
      (NativeBatch.additionalSpace N axis + tailAdditionalSpace N axis)
    change _ ≤ base.auxiliarySpace axis + NativeBatch.additionalSpace N axis at bound
    omega
  · have tailBound := tail_auxiliary_le base noQuantum input path.2
    have nativeBound := nativeContext_auxiliary_le base noQuantum N
    intro axis
    exact (tailBound axis).trans ((Nat.add_le_add_right (nativeBound axis) _).trans_eq
      (Nat.add_assoc _ _ _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
