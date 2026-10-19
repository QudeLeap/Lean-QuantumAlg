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
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Sequential reset of an existing physical register

Each item is the existing physical-wire and classical-result-cell pair used
for Z readout. Its actual reset is the existing measurement, stored selection
and cyclic correction circuit [dW19, qcnotes.tex:5405,5409,5420]. The list may
reuse one result cell and may revisit wires. No instruction allocates or
releases a quantum system or a classical cell.

Every reset contributes its measurement and the complete native expansion of
its selected correction, including a zero shift. Independent budgets bound
each supplied correction; exact trace and depth recurrences use the selected
realization on the actual path.
The empty sequence retains the same complete live context and emits no event.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
variable {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}

variable (implementations : ∀ wire,
  QuditShift.Realizations gates oracles ctx.quantumLayout wire)

/-- Execute the actual measurement-and-correction circuits in the given order. -/
def sequence (readouts : List (ZReadout ctx))
    (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty)
    (allowAllocation : Bool := true) :
    Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation :=
  match readouts with
  | [] => .id (model := .quantum gates oracles operations services) ctx
  | head :: tail => .seq
      (circuit (allowAllocation := allowAllocation) (services := services)
        head.wire head.output (implementations head.wire) operations)
      (sequence (allowAllocation := allowAllocation) (services := services) tail operations)

/-- Every nonempty reset sequence records the first physical Z measurement
on every path, independently of the selected correction or remaining resets. -/
lemma sequence_measured {allowAllocation : Bool}
    (head : ZReadout ctx) (tail : List (ZReadout ctx))
    (operations : ClassicalOpModel)
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        (head :: tail) operations).Path) :
    Resource.Event.measurement (model := .quantum gates oracles operations services)
      (ctx.quantumLayout.wire head.wire).dimension ∈
      (sequence (allowAllocation := allowAllocation) (services := services) implementations (head ::
          tail) operations).eventTrace path
        := by
  change Resource.Event.measurement (model := .quantum gates oracles operations services)
      (ctx.quantumLayout.wire head.wire).dimension ∈
    (circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
        (implementations head.wire)
      operations).eventTrace
      path.1 ++ (sequence (allowAllocation := allowAllocation) (services := services)
          implementations tail operations).eventTrace path.2
  apply List.mem_append.mpr
  left
  rw [zReset_eventTrace (allowAllocation := allowAllocation)]
  exact List.mem_cons_self

/-- Nonemptiness is the precise generic condition for a reset sequence to
contain a physical measurement on every path. -/
lemma sequence_measured_of_nonempty {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (operations : ClassicalOpModel) (nonempty : readouts ≠ [])
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    ∃ dimension : ℕ+,
      Resource.Event.measurement
        (model := .quantum gates oracles operations services) dimension ∈
        (sequence (allowAllocation := allowAllocation) (services := services) implementations
            readouts operations).eventTrace path := by
  cases readouts with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      exact ⟨(ctx.quantumLayout.wire head.wire).dimension,
        sequence_measured (allowAllocation := allowAllocation) implementations head tail operations
            path⟩

/-- An empty sequence preserves the full quantum and external-reference marginal. -/
lemma sequence_nil_quantumMarginal {allowAllocation : Bool}
    {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History)) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations
        []).execute environment Reference state).quantumMarginal =
      state.quantumMarginal := by
  change ((Circuit.id (allowAllocation := allowAllocation) (model := .quantum gates oracles .empty
      services) ctx).execute environment Reference state).quantumMarginal = state.quantumMarginal
  calc
    _ = (state.mapHistory
        (fun history => (history.1, (history.2, ())))).quantumMarginal := by
      rw [Circuit.execute_id]
      apply congrArg ExecutionState.quantumMarginal
      exact ExecutionState.executionState_mapClassical_congr_decision
        state _ _ (fun _ => rfl) _ _
    _ = _ := State.mapHistory_quantumMarginal state _

variable {operations : ClassicalOpModel}

/-- An independent sum of the dimension-indexed native correction envelopes. -/
def sequenceEnvelope (readouts : List (ZReadout ctx))
    (correctionBudget : ZReadout ctx → ResourcePool (.quantum gates oracles operations services)) :
    ResourcePool (.quantum gates oracles operations services) :=
  (readouts.map (fun item =>
    eventEnvelope (ctx.quantumLayout.wire item.wire).dimension
      (correctionBudget item))).sum

/-- An independent serial duration bound for the same declared wire dimensions. -/
def sequenceDepthEnvelope (readouts : List (ZReadout ctx))
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat)
    (correctionDepth : ZReadout ctx → Nat) : Nat :=
  (readouts.map (fun item =>
    depthEnvelope (ctx.quantumLayout.wire item.wire).dimension duration
      (correctionDepth item))).sum

/-- The selected native ledger is bounded at every event coordinate. -/
lemma zReset_sequence_resourcePool_le {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (correctionBudget : ZReadout ctx → ResourcePool (.quantum gates oracles operations services))
    (bounded : ∀ item amount,
      ResourcePool.ofList ((implementations item.wire amount).circuit.eventTrace operations
        services) ≤
        correctionBudget item)
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).resourcePool path ≤
      sequenceEnvelope readouts correctionBudget := by
  induction readouts with
  | nil => exact le_refl 0
  | cons head tail ih =>
      change ResourcePool.ofList
        ((circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
            (implementations head.wire)
          operations).eventTrace path.1 ++
          (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
              operations).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      exact add_le_add
        (zReset_resourcePool_le_envelope (allowAllocation := allowAllocation) head.wire head.output
          (implementations head.wire) (correctionBudget head) (bounded head) path.1)
        (ih path.2)

/-- One stage contributes one Z event and the selected native correction trace. -/
lemma zReset_sequence_eventTrace_length {allowAllocation : Bool} (head : ZReadout ctx)
    (tail : List (ZReadout ctx))
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        (head :: tail) operations).Path) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations (head ::
        tail) operations).eventTrace
      path).length =
      1 + ((implementations head.wire
        (-(readOutcome (allowAllocation := allowAllocation) (services := services) (operations :=
            operations) head.wire head.output
          (implementations head.wire) path.1))).circuit.eventTrace operations services).length +
        ((sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations).eventTrace
          path.2).length := by
  change ((circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
      (implementations head.wire)
    operations).eventTrace
      path.1 ++
    (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
        operations).eventTrace path.2).length = _
  rw [List.length_append, zReset_eventTrace_length (allowAllocation := allowAllocation)]

/-- Unit duration is the measurement followed by the selected correction and remaining stages. -/
lemma zReset_sequence_unitDepth {allowAllocation : Bool} (head : ZReadout ctx)
    (tail : List (ZReadout ctx))
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        (head :: tail) operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations (head ::
        tail) operations).depth (fun _ => 1)
      path =
      1 + DepthExpr.depthEval (fun _ => 1) ((implementations head.wire
        (-(readOutcome (allowAllocation := allowAllocation) (services := services) (operations :=
            operations) head.wire head.output
          (implementations head.wire) path.1))).circuit.eventDepth operations services) +
        (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations).depth (fun _ => 1) path.2
          := by
  change (circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
      (implementations head.wire)
    operations).depth
      (fun _ => 1) path.1 +
    (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
        operations).depth (fun _ => 1) path.2 = _
  rw [zReset_unitDepth (allowAllocation := allowAllocation)]

/-- General durations retain every sequential measurement-to-correction dependency. -/
lemma zReset_sequence_depth_le {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat)
    (correctionDepth : ZReadout ctx → Nat)
    (bounded : ∀ item amount,
      DepthExpr.depthEval duration
        ((implementations item.wire amount).circuit.eventDepth operations services) ≤
        correctionDepth item)
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).depth duration path ≤
      sequenceDepthEnvelope readouts duration correctionDepth := by
  induction readouts with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      change (circuit (allowAllocation := allowAllocation) (services := services) head.wire
          head.output (implementations head.wire)
        operations).depth
          duration path.1 +
        (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations).depth duration path.2 ≤ _
      exact Nat.add_le_add
        (zReset_depth_le_envelope (allowAllocation := allowAllocation) head.wire head.output
            (implementations head.wire)
          duration (correctionDepth head) (bounded head) path.1)
        (ih path.2)

/-- Every live context is exactly the original register and its actual result cells. -/
lemma zReset_sequence_visitedContexts {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).visitedContexts path =
      List.replicate (2 * readouts.length + 1) ctx := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change (circuit (allowAllocation := allowAllocation) (services := services) head.wire
          head.output (implementations head.wire)
        operations).visitedContexts
          path.1 ++
        (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations).visitedContexts path.2 = _
      rw [zReset_visitedContexts (allowAllocation := allowAllocation), ih]
      have lengthEq : 2 * (head :: tail).length + 1 = 2 * tail.length + 1 + 2 := by
        simp only [List.length_cons]
        omega
      rw [lengthEq]
      rfl

/-- The whole sequence has exactly the same resident space, including reused classical cells. -/
lemma zReset_sequence_peakResidentSpace {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).peakResidentSpace path =
      ctx.residentSpace := by
  induction readouts with
  | nil =>
      change SpacePool.max ctx.residentSpace 0 = ctx.residentSpace
      exact SpacePool.max_zero _
  | cons head tail ih =>
      refine (Circuit.peakResidentSpace_seq
        (circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
            (implementations head.wire)
          operations)
        (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations) (path.1, path.2)).trans ?_
      rw [zReset_peakResidentSpace (allowAllocation := allowAllocation), ih]
      exact SpacePool.max_self _

/-- Actual auxiliary roles remain unchanged on every selected path. -/
lemma zReset_sequence_peakAuxiliarySpace {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (path : (sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts operations).Path) :
    (sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  induction readouts with
  | nil =>
      change SpacePool.max ctx.auxiliarySpace 0 = ctx.auxiliarySpace
      exact SpacePool.max_zero _
  | cons head tail ih =>
      refine (Circuit.peakAuxiliarySpace_seq
        (circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
            (implementations head.wire)
          operations)
        (sequence (allowAllocation := allowAllocation) (services := services) implementations tail
            operations) (path.1, path.2)).trans ?_
      rw [zReset_peakAuxiliarySpace (allowAllocation := allowAllocation), ih]
      exact SpacePool.max_self _

/-- Every external-reference matrix entry survives the actual sequential resets. -/
lemma zReset_sequence_reference_entry {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((sequence (allowAllocation := allowAllocation) (services := services) implementations
          readouts).execute environment Reference
        state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : ctx.register.Index, state.quantumMarginal.matrix (basis, left) (basis, right) := by
  induction readouts generalizing History with
  | nil =>
      rw [sequence_nil_quantumMarginal (allowAllocation := allowAllocation)]
  | cons head tail ih =>
      rw [sequence, Circuit.execute_seq,
          State.mapHistory_quantumMarginal, ih]
      exact zReset_reference_entry (allowAllocation := allowAllocation) head.wire head.output
          (implementations head.wire)
        state left right

end

end QuantumAlg.ZReset
