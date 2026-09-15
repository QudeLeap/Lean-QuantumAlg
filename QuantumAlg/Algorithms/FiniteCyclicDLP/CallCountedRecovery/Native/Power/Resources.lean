/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Power
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources

/-!
# Actual group-power call counts, duration and accumulator space

Every original position executes one square and at most one multiplication.
The independent envelope reserves both distinct declarations. Actual paths
record the stored-bit choice, and every duration follows that same serial
trace. The scan itself allocates nothing; its wrapper retains exactly one
fresh word through the caller continuation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- One independent square site and one possible multiplication site. -/
def powerSiteEnvelope (A : Access G width) : ResourcePool .quantum :=
  ResourcePool.singleton (.classicalSubroutine A.squareLabel) +
    ResourcePool.singleton (.classicalSubroutine A.multiplyLabel)

/-- The actual branch contributes its multiplication after the mandatory square. -/
theorem groupPowerStep_eventTrace (A : Access G width) (generator : G)
    (bit : CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerStep A generator bit accumulator writable).Path) :
    (powerStep A generator bit accumulator writable).eventTrace path =
      [.classicalSubroutine A.squareLabel] ++
        (if path.2.1.toBool then [.classicalSubroutine A.multiplyLabel] else []) := by
  rcases path with ⟨_, ⟨value, chosen⟩⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Arbitrary durations charge the same actual square and optional multiplication. -/
theorem groupPowerStep_depth (A : Access G width) (generator : G)
    (bit : CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (duration : Resource.Event .quantum → Nat)
    (path : (powerStep A generator bit accumulator writable).Path) :
    (powerStep A generator bit accumulator writable).depth duration path =
      duration (.classicalSubroutine A.squareLabel) +
        (if path.2.1.toBool then duration (.classicalSubroutine A.multiplyLabel) else 0) := by
  rcases path with ⟨_, ⟨value, chosen⟩⟩
  cases value with
  | bit value => cases value <;> rfl

/-- The original pair of distinct declared labels bounds every actual branch. -/
theorem groupPowerStep_pool_le (A : Access G width) (generator : G)
    (bit : CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerStep A generator bit accumulator writable).Path) :
    (powerStep A generator bit accumulator writable).resourcePool path ≤ powerSiteEnvelope A := by
  rw [Circuit.resourcePool, groupPowerStep_eventTrace, ResourcePool.ofList_append]
  unfold powerSiteEnvelope
  split
  · exact le_rfl
  · exact le_add_of_nonneg_right zero_le

/-- Every actual position executes exactly one square, independently of its branch value. -/
theorem groupPowerRange_square_count (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    ResourcePool.count (.classicalSubroutine A.squareLabel)
      ((powerRange A generator count bits accumulator writable).resourcePool path) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change ResourcePool.count (.classicalSubroutine A.squareLabel)
        (ResourcePool.ofList ((powerStep A generator (bits 0) accumulator writable).eventTrace
          path.1 ++ (powerRange A generator count (fun index => bits index.succ)
            accumulator writable).eventTrace path.2)) = count + 1
      rw [ResourcePool.ofList_append, ResourcePool.count_add,
        show ResourcePool.count (.classicalSubroutine A.squareLabel)
          (ResourcePool.ofList ((powerRange A generator count (fun index => bits index.succ)
            accumulator writable).eventTrace path.2)) = count from ih _ path.2,
        groupPowerStep_eventTrace]
      split <;> simp [ResourcePool.ofList, ResourcePool.count, A.square_ne_multiply, Nat.add_comm]

/-- The complete actual scan is bounded by one pair of sites per position. -/
theorem groupPowerRange_pool_le (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    (powerRange A generator count bits accumulator writable).resourcePool path ≤
      ResourcePool.scale count (powerSiteEnvelope A) :=
  Circuit.forRange_pool_le count _ (powerSiteEnvelope A)
    (fun index => groupPowerStep_pool_le A generator (bits index) accumulator writable) path

/-- Actual multiplication is bounded by the number of tested bits, without claiming equality. -/
theorem groupPowerRange_multiply_count_le (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    ResourcePool.count (.classicalSubroutine A.multiplyLabel)
      ((powerRange A generator count bits accumulator writable).resourcePool path) ≤ count := by
  have bounded := ResourcePool.le_iff_count.mp
    (groupPowerRange_pool_le A generator count bits accumulator writable path)
    (.classicalSubroutine A.multiplyLabel)
  simpa [powerSiteEnvelope, ResourcePool.count_scale, ResourcePool.count_add,
    ResourcePool.count_singleton, A.square_ne_multiply, Ne.symm A.square_ne_multiply] using bounded

/-- The entire scan's dependency depth is exactly its actual trace duration. -/
theorem groupPowerRange_duration (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (duration : Resource.Event .quantum → Nat)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    (powerRange A generator count bits accumulator writable).depth duration path =
      (((powerRange A generator count bits accumulator writable).eventTrace path).map
        duration).sum := by
  apply Circuit.forRange_duration_eventTrace
  intro index selected
  rw [groupPowerStep_depth, groupPowerStep_eventTrace]
  split <;> simp

/-- Independent serial duration reserves both possible declared calls at each original site. -/
theorem groupPowerRange_depth_le (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (duration : Resource.Event .quantum → Nat)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    (powerRange A generator count bits accumulator writable).depth duration path ≤
      count * (duration (.classicalSubroutine A.squareLabel) +
        duration (.classicalSubroutine A.multiplyLabel)) := by
  have bounded := Circuit.forRange_depth_le_sum count
    (fun index => powerStep A generator (bits index) accumulator writable) duration
    (fun _ => duration (.classicalSubroutine A.squareLabel) +
      duration (.classicalSubroutine A.multiplyLabel))
    (fun index selected => by rw [groupPowerStep_depth]; split <;> omega) path
  simpa [powerRange] using bounded

private theorem step_visits (A : Access G width) (generator : G) (bit : CInputRef ctx .bit)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerStep A generator bit accumulator writable).Path) :
    (powerStep A generator bit accumulator writable).visitedContexts path = [ctx, ctx] := by
  rcases path with ⟨_, ⟨value, chosen⟩⟩
  cases value with
  | bit value => cases value <;> rfl

/-- The existing caller context includes every live cell throughout the unallocated scan. -/
theorem groupPowerRange_resident_le (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    (powerRange A generator count bits accumulator writable).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.forRange_resident_le count _ _ le_rfl
  intro index selected
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited member
  rw [step_visits] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact le_rfl
  · have same := List.mem_singleton.mp member
    simpa only [same] using (le_refl visited.residentSpace)

/-- The same actual path adds no auxiliary cell to its full caller context. -/
theorem groupPowerRange_auxiliary_le (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (path : (powerRange A generator count bits accumulator writable).Path) :
    (powerRange A generator count bits accumulator writable).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.forRange_auxiliary_le count _ _ le_rfl
  intro index selected
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited member
  rw [step_visits] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact le_rfl
  · have same := List.mem_singleton.mp member
    simpa only [same] using (le_refl visited.auxiliarySpace)


variable (A : Access G width) (generator : G)
    (candidate : CInputRef ctx (.unsignedWord width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord width) →
      Transport ctx inner → Circuit inner inner)

/-- The fresh accumulator introduces no event beyond the actual scan and continuation. -/
theorem withPowerAccumulator_pool_le (additional : ResourcePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (input : CInputRef inner (.unsignedWord width))
      (transport : Transport ctx inner) (path : (body input transport).Path),
      (body input transport).resourcePool path ≤ additional)
    (path : (withPowerAccumulator A generator candidate body).Path) :
    (withPowerAccumulator A generator candidate body).resourcePool path ≤
      ResourcePool.scale (width - 1) (powerSiteEnvelope A) + additional := by
  apply withCellsFrom_pool_le
  intro inner cells distinct transport separated selected
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (groupPowerRange_pool_le A generator (width - 1)
    (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
    cells.head.ref (Or.inl cells.head.role) selected.1) (bodyBound _ _ selected.2)

/-- Actual arbitrary durations include the continuation while keeping the original bit count. -/
theorem withPowerAccumulator_depth_le (duration : Resource.Event .quantum → Nat)
    (additional : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (input : CInputRef inner (.unsignedWord width))
      (transport : Transport ctx inner) (path : (body input transport).Path),
      (body input transport).depth duration path ≤ additional)
    (path : (withPowerAccumulator A generator candidate body).Path) :
    (withPowerAccumulator A generator candidate body).depth duration path ≤
      (width - 1) * (duration (.classicalSubroutine A.squareLabel) +
        duration (.classicalSubroutine A.multiplyLabel)) + additional := by
  apply withCellsFrom_depth_le
  intro inner cells distinct transport separated selected
  change _ + _ ≤ _
  exact Nat.add_le_add (groupPowerRange_depth_le A generator (width - 1)
    (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
    cells.head.ref (Or.inl cells.head.role) duration selected.1) (bodyBound _ _ selected.2)

/-- One real accumulator remains live through the continuation's complete resident peak. -/
theorem withPowerAccumulator_resident_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (input : CInputRef inner (.unsignedWord width))
      (transport : Transport ctx inner) (path : (body input transport).Path),
      (body input transport).peakResidentSpace path ≤ additional + inner.residentSpace)
    (path : (withPowerAccumulator A generator candidate body).Path) :
    (withPowerAccumulator A generator candidate body).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + additional + ctx.residentSpace := by
  have bounded := withCellsFrom_resident_le (Transport.id ctx) [.unsignedWord width]
    (fun cells _ transport _ =>
      .seq (powerScan A generator (transport.liftInput candidate) cells.head.ref
        (Or.inl cells.head.role)) (body (powerRead cells.head.ref) transport)) additional
    (by
      intro inner cells distinct transport separated selected
      rw [Circuit.peakResidentSpace_seq]
      refine SpacePool.max_le ?_ (bodyBound _ _ selected.2)
      exact (groupPowerRange_resident_le A generator (width - 1)
        (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
        cells.head.ref (Or.inl cells.head.role) selected.1).trans
          (le_add_of_nonneg_left zero_le)) path
  simpa only [withPowerAccumulator, withCells, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] using bounded

/-- One real accumulator remains live through the continuation's complete auxiliary peak. -/
theorem withPowerAccumulator_auxiliary_le (additional : SpacePool .quantum)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (input : CInputRef inner (.unsignedWord width))
      (transport : Transport ctx inner) (path : (body input transport).Path),
      (body input transport).peakAuxiliarySpace path ≤ additional + inner.auxiliarySpace)
    (path : (withPowerAccumulator A generator candidate body).Path) :
    (withPowerAccumulator A generator candidate body).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + additional + ctx.auxiliarySpace := by
  have bounded := withCellsFrom_auxiliary_le (Transport.id ctx) [.unsignedWord width]
    (fun cells _ transport _ =>
      .seq (powerScan A generator (transport.liftInput candidate) cells.head.ref
        (Or.inl cells.head.role)) (body (powerRead cells.head.ref) transport)) additional
    (by
      intro inner cells distinct transport separated selected
      rw [Circuit.peakAuxiliarySpace_seq]
      refine SpacePool.max_le ?_ (bodyBound _ _ selected.2)
      exact (groupPowerRange_auxiliary_le A generator (width - 1)
        (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
        cells.head.ref (Or.inl cells.head.role) selected.1).trans
          (le_add_of_nonneg_left zero_le)) path
  simpa only [withPowerAccumulator, withCells, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] using bounded

/-- Serial continuation durations remain the durations of the very same allocated path. -/
theorem withPowerAccumulator_duration (duration : Resource.Event .quantum → Nat)
    (bodyExact : ∀ {inner : RuntimeCtx .quantum} (input : CInputRef inner (.unsignedWord width))
      (transport : Transport ctx inner) (path : (body input transport).Path),
      (body input transport).depth duration path =
        (((body input transport).eventTrace path).map duration).sum)
    (path : (withPowerAccumulator A generator candidate body).Path) :
    (withPowerAccumulator A generator candidate body).depth duration path =
      (((withPowerAccumulator A generator candidate body).eventTrace path).map duration).sum := by
  have exactPath := withCellsFrom_property (Transport.id ctx) [.unsignedWord width]
    (fun cells _ transport _ =>
      .seq (powerScan A generator (transport.liftInput candidate) cells.head.ref
        (Or.inl cells.head.role)) (body (powerRead cells.head.ref) transport))
    (fun _ code => ∀ selected : code.Path,
      code.depth duration selected = ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available) (by
      intro inner cells distinct transport separated selected
      change _ + _ = (List.map duration (_ ++ _)).sum
      rw [List.map_append, List.sum_append]
      exact congrArg₂ (· + ·) (groupPowerRange_duration A generator (width - 1)
        (fun index => .wordBitGet (transport.liftInput candidate) (tailIndex width index))
        cells.head.ref (Or.inl cells.head.role) duration selected.1)
          (bodyExact _ _ selected.2))
  exact exactPath path

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
