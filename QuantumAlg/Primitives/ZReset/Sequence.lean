/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Primitives.ZReset.Reference
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Sequential reset of an existing physical register

Each item is the existing physical-wire and classical-result-cell pair used
for Z readout. Its actual reset is the existing measurement, stored selection
and cyclic correction circuit [dW19, qcnotes.tex:5405,5409,5420]. The list may
reuse one result cell and may revisit wires. No instruction allocates or
releases a quantum system or a classical cell.

Every reset contributes its measurement and selected shift, including a zero
shift. The independent envelope includes all finite correction alternatives;
the exact event count and unit-duration depth count only the executed pair.
The empty sequence retains the same complete live context and emits no event.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- Execute the actual measurement-and-correction circuits in the given order. -/
def sequence : List (ZReadout ctx) → Circuit ctx ctx
  | [] => .id ctx
  | head :: tail => .seq (circuit head.wire head.output) (sequence tail)

/-- An independent sum of the dimension-indexed native correction envelopes. -/
def sequenceEnvelope (readouts : List (ZReadout ctx)) : ResourcePool .quantum :=
  (readouts.map (fun item => eventEnvelope (ctx.quantumLayout.wire item.wire).dimension)).sum

/-- An independent serial duration bound for the same declared wire dimensions. -/
def sequenceDepthEnvelope (readouts : List (ZReadout ctx))
    (duration : Resource.Event .quantum → Nat) : Nat :=
  (readouts.map (fun item =>
    depthEnvelope (ctx.quantumLayout.wire item.wire).dimension duration)).sum

/-- The selected native ledger is bounded at every event coordinate. -/
theorem zReset_sequence_resourcePool_le (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    (sequence readouts).resourcePool path ≤ sequenceEnvelope readouts := by
  induction readouts with
  | nil => exact le_refl 0
  | cons head tail ih =>
      change ResourcePool.ofList
        ((circuit head.wire head.output).eventTrace path.1 ++
          (sequence tail).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      exact add_le_add (zReset_resourcePool_le_envelope head.wire head.output path.1) (ih path.2)

/-- Exact executed events count both the measurement and its selected correction. -/
theorem zReset_sequence_eventTrace_length (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    ((sequence readouts).eventTrace path).length = 2 * readouts.length := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change ((circuit head.wire head.output).eventTrace path.1 ++
        (sequence tail).eventTrace path.2).length = 2 * (tail.length + 1)
      rw [List.length_append, zReset_eventTrace_length, ih]
      omega

/-- Unit-duration serial depth equals the actual two events per reset. -/
theorem zReset_sequence_unitDepth (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    (sequence readouts).depth (fun _ => 1) path = 2 * readouts.length := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change (circuit head.wire head.output).depth (fun _ => 1) path.1 +
        (sequence tail).depth (fun _ => 1) path.2 = 2 * (tail.length + 1)
      rw [zReset_unitDepth, ih]
      omega

/-- General durations retain every sequential measurement-to-correction dependency. -/
theorem zReset_sequence_depth_le (readouts : List (ZReadout ctx))
    (duration : Resource.Event .quantum → Nat) (path : (sequence readouts).Path) :
    (sequence readouts).depth duration path ≤ sequenceDepthEnvelope readouts duration := by
  induction readouts with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      change (circuit head.wire head.output).depth duration path.1 +
        (sequence tail).depth duration path.2 ≤ _
      exact Nat.add_le_add (zReset_depth_le_envelope head.wire head.output duration path.1)
        (ih path.2)

/-- Every live context is exactly the original register and its actual result cells. -/
theorem zReset_sequence_visitedContexts (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    (sequence readouts).visitedContexts path = List.replicate (2 * readouts.length + 1) ctx := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change (circuit head.wire head.output).visitedContexts path.1 ++
        (sequence tail).visitedContexts path.2 = _
      rw [zReset_visitedContexts, ih]
      have lengthEq : 2 * (head :: tail).length + 1 = 2 * tail.length + 1 + 2 := by
        simp only [List.length_cons]
        omega
      rw [lengthEq]
      rfl

/-- The whole sequence has exactly the same resident space, including reused classical cells. -/
theorem zReset_sequence_peakResidentSpace (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    (sequence readouts).peakResidentSpace path = ctx.residentSpace := by
  induction readouts with
  | nil =>
      change SpacePool.max ctx.residentSpace 0 = ctx.residentSpace
      exact SpacePool.max_zero _
  | cons head tail ih =>
      refine (Circuit.peakResidentSpace_seq (circuit head.wire head.output)
        (sequence tail) (path.1, path.2)).trans ?_
      rw [zReset_peakResidentSpace, ih]
      exact SpacePool.max_self _

/-- Actual auxiliary roles remain unchanged on every selected path. -/
theorem zReset_sequence_peakAuxiliarySpace (readouts : List (ZReadout ctx))
    (path : (sequence readouts).Path) :
    (sequence readouts).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  induction readouts with
  | nil =>
      change SpacePool.max ctx.auxiliarySpace 0 = ctx.auxiliarySpace
      exact SpacePool.max_zero _
  | cons head tail ih =>
      refine (Circuit.peakAuxiliarySpace_seq (circuit head.wire head.output)
        (sequence tail) (path.1, path.2)).trans ?_
      rw [zReset_peakAuxiliarySpace, ih]
      exact SpacePool.max_self _

/-- Every external-reference matrix entry survives the actual sequential resets. -/
theorem zReset_sequence_reference_entry (readouts : List (ZReadout ctx))
    {Reference : Register} {History : Type} [Fintype History] (state : State ctx Reference History)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((sequence readouts).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : ctx.register.Index, state.quantumMarginal.matrix (basis, left) (basis, right) := by
  induction readouts generalizing History with
  | nil =>
      rw [sequence, Circuit.execute_id, State.skip_quantumMarginal]
  | cons head tail ih =>
      rw [sequence, Circuit.execute_seq, State.mapHistory_quantumMarginal, ih]
      exact zReset_reference_entry head.wire head.output state left right

end

end QuantumAlg.ZReset
