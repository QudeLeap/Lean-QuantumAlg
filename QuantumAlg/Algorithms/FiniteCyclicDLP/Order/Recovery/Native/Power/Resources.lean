/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power
public import QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Query resources of representation-independent group powering

Every attempt explicitly resets the hidden accumulator, performs one square
and at most one generator multiplication per exponent bit, then compares with
the target. These are caller-visible query counts and abstract dependency
steps; the black-box group's encoding, storage and internal work are absent.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- The classical-oracle event that resets the hidden group accumulator. -/
@[expose] public def resetEvent : Resource.Event (OrderExecution.model P) :=
  .classicalQuery .reset

/-- The classical-oracle event that performs one group operation. -/
@[expose] public def groupOperationEvent : Resource.Event (OrderExecution.model P) :=
  .classicalQuery .groupOperation

/-- The classical-oracle event that compares the accumulator with the target. -/
@[expose] public def equalityTestEvent : Resource.Event (OrderExecution.model P) :=
  .classicalQuery .equalityTest

/-- The independent allowance for the two possible group operations at one bit. -/
@[expose] public def powerSiteEnvelope : ResourcePool (OrderExecution.model P) :=
  ResourcePool.singleton (groupOperationEvent P) +
    ResourcePool.singleton (groupOperationEvent P)

/-- The reset, per-bit group-operation, and equality-query allowance for one power check. -/
@[expose] public def powerCheckEnvelope (width : Nat) : ResourcePool (OrderExecution.model P) :=
  ResourcePool.singleton (resetEvent P) +
    (ResourcePool.scale width (powerSiteEnvelope P) +
      ResourcePool.singleton (equalityTestEvent P))

/-- The independent allowance charges both possible group operations at one
powering site. -/
@[simp] public theorem powerSiteEnvelope_groupOperation_count :
    ResourcePool.count (groupOperationEvent P) (powerSiteEnvelope P) = 2 := by
  simp [powerSiteEnvelope]

/-- A complete checked power allowance charges two group operations per
candidate bit; reset and equality remain distinct query coordinates. -/
@[simp] public theorem powerCheckEnvelope_groupOperation_count (width : Nat) :
    ResourcePool.count (groupOperationEvent P) (powerCheckEnvelope P width) =
      2 * width := by
  simp [powerCheckEnvelope, powerSiteEnvelope, resetEvent, groupOperationEvent,
    equalityTestEvent]
  omega

public theorem resetQuery_eventTrace (result : CWriteRef ctx .bit)
    (path : (resetQuery P result).Path) :
    (resetQuery P result).eventTrace path = [resetEvent P] := rfl

public theorem squareQuery_eventTrace (result : CWriteRef ctx .bit)
    (path : (squareQuery P result).Path) :
    (squareQuery P result).eventTrace path = [groupOperationEvent P] := rfl

public theorem multiplyGeneratorQuery_eventTrace (result : CWriteRef ctx .bit)
    (path : (multiplyGeneratorQuery P result).Path) :
    (multiplyGeneratorQuery P result).eventTrace path = [groupOperationEvent P] := rfl

public theorem targetEqualityQuery_eventTrace (result : CWriteRef ctx .bit)
    (path : (targetEqualityQuery P result).Path) :
    (targetEqualityQuery P result).eventTrace path = [equalityTestEvent P] := rfl

public theorem powerStep_eventTrace (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit) (path : (powerStep P bit result).Path) :
    (powerStep P bit result).eventTrace path =
      [groupOperationEvent P] ++
        (if path.2.1.toBool then [groupOperationEvent P] else []) := by
  rcases path with ⟨square, ⟨value, selected⟩⟩
  cases value with
  | bit value => cases value <;> rfl

public theorem powerStep_depth (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (powerStep P bit result).Path) :
    (powerStep P bit result).depth duration path =
      duration (groupOperationEvent P) +
        (if path.2.1.toBool then duration (groupOperationEvent P) else 0) := by
  rcases path with ⟨square, ⟨value, selected⟩⟩
  cases value with
  | bit value => cases value <;> rfl

public theorem powerStep_pool_le (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit) (path : (powerStep P bit result).Path) :
    (powerStep P bit result).resourcePool path ≤ powerSiteEnvelope P := by
  rw [Circuit.resourcePool, powerStep_eventTrace, ResourcePool.ofList_append]
  unfold powerSiteEnvelope
  split
  · exact le_rfl
  · exact le_add_of_nonneg_right zero_le

public theorem powerScan_pool_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerScan P candidate result).Path) :
    (powerScan P candidate result).resourcePool path ≤
      ResourcePool.scale width (powerSiteEnvelope P) :=
  Circuit.forRange_pool_le width _ (powerSiteEnvelope P)
    (fun index => powerStep_pool_le P (.wordBitGet candidate index) result) path

public theorem powerScan_depth_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (powerScan P candidate result).Path) :
    (powerScan P candidate result).depth duration path ≤
      width * (duration (groupOperationEvent P) + duration (groupOperationEvent P)) := by
  have bounded := Circuit.forRange_depth_le_sum width
    (fun index => powerStep P (.wordBitGet candidate index) result) duration
    (fun _ => duration (groupOperationEvent P) + duration (groupOperationEvent P))
    (fun index selected => by rw [powerStep_depth]; split <;> omega) path
  simpa [powerScan] using bounded

public theorem powerCheck_pool_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerCheck P candidate result).Path) :
    (powerCheck P candidate result).resourcePool path ≤ powerCheckEnvelope P width := by
  change ResourcePool.ofList (_ ++ (_ ++ _)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append,
    resetQuery_eventTrace, targetEqualityQuery_eventTrace]
  exact add_le_add le_rfl (add_le_add (powerScan_pool_le P candidate result path.2.1) le_rfl)

public theorem powerCheck_depth_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (duration : Resource.Event (OrderExecution.model P) → Nat)
    (path : (powerCheck P candidate result).Path) :
    (powerCheck P candidate result).depth duration path ≤
      duration (resetEvent P) +
        (width * (duration (groupOperationEvent P) + duration (groupOperationEvent P)) +
          duration (equalityTestEvent P)) := by
  change _ + (_ + _) ≤ _
  exact Nat.add_le_add le_rfl
    (Nat.add_le_add (powerScan_depth_le P candidate result duration path.2.1) le_rfl)

/-- One square and the selected multiplication use only existing caller-visible storage. -/
public theorem powerStep_resident_le (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit) (path : (powerStep P bit result).Path) :
    (powerStep P bit result).peakResidentSpace path ≤ ctx.residentSpace := by
  rcases path with ⟨squarePath, ⟨value, selectedPath⟩⟩
  unfold powerStep
  rw [Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le (le_of_eq
    (Circuit.peakResidentSpace_classicalQuery _ squarePath)) ?_
  rw [Circuit.peakResidentSpace_branch]
  cases value with
  | bit value =>
      cases value
      · simpa only [multiplyChoice] using le_of_eq
          (Circuit.peakResidentSpace_id (model := OrderExecution.model P) selectedPath)
      · simpa only [multiplyChoice, multiplyGeneratorQuery] using le_of_eq
          (Circuit.peakResidentSpace_classicalQuery _ selectedPath)

/-- The hidden power step likewise allocates no caller-visible auxiliary cell. -/
public theorem powerStep_auxiliary_le (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit) (path : (powerStep P bit result).Path) :
    (powerStep P bit result).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  rcases path with ⟨squarePath, ⟨value, selectedPath⟩⟩
  unfold powerStep
  rw [Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le (le_of_eq
    (Circuit.peakAuxiliarySpace_classicalQuery _ squarePath)) ?_
  rw [Circuit.peakAuxiliarySpace_branch]
  cases value with
  | bit value =>
      cases value
      · simpa only [multiplyChoice] using le_of_eq
          (Circuit.peakAuxiliarySpace_id (model := OrderExecution.model P) selectedPath)
      · simpa only [multiplyChoice, multiplyGeneratorQuery] using le_of_eq
          (Circuit.peakAuxiliarySpace_classicalQuery _ selectedPath)

/-- Reusing the result bit through the full scan leaves resident space unchanged. -/
public theorem powerScan_resident_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerScan P candidate result).Path) :
    (powerScan P candidate result).peakResidentSpace path ≤ ctx.residentSpace :=
  Circuit.forRange_resident_le (model := OrderExecution.model P) width _ ctx.residentSpace le_rfl
    (fun index => powerStep_resident_le P (.wordBitGet candidate index) result) path

/-- Reusing the same bit through the scan leaves auxiliary space unchanged. -/
public theorem powerScan_auxiliary_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerScan P candidate result).Path) :
    (powerScan P candidate result).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  Circuit.forRange_auxiliary_le (model := OrderExecution.model P) width _ ctx.auxiliarySpace le_rfl
    (fun index => powerStep_auxiliary_le P (.wordBitGet candidate index) result) path

/-- Reset, hidden powering and comparison add no caller-visible resident storage. -/
public theorem powerCheck_resident_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerCheck P candidate result).Path) :
    (powerCheck P candidate result).peakResidentSpace path ≤ ctx.residentSpace := by
  unfold powerCheck
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakResidentSpace_classicalQuery _ path.1))
    (SpacePool.max_le (powerScan_resident_le P candidate result path.2.1)
      (le_of_eq (Circuit.peakResidentSpace_classicalQuery _ path.2.2)))

/-- The same full service check adds no caller-visible auxiliary storage. -/
public theorem powerCheck_auxiliary_le {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (path : (powerCheck P candidate result).Path) :
    (powerCheck P candidate result).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  unfold powerCheck
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakAuxiliarySpace_classicalQuery _ path.1))
    (SpacePool.max_le (powerScan_auxiliary_le P candidate result path.2.1)
      (le_of_eq (Circuit.peakAuxiliarySpace_classicalQuery _ path.2.2)))

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
