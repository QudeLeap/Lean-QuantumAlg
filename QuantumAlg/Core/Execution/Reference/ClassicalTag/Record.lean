/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Operations
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Tag slices of actual sampled and measured store writes

These laws combine the existing sampling or measurement with its actual finite
record update. The tag is retained beside the old history even when the store
update identifies records. No branch normalization or independent-state
assumption is used.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H K Outcome : Type} [Fintype H] [Fintype K] [Fintype Outcome]

/-- Tag decoding is independent of equality-decision choices at both record boundaries. -/
lemma decodeReferenceTag_mapRecord_decisions
    {beforeMap : DecidableEq (Store ctx × K)}
    {afterMap : DecidableEq (Store ctx × (K × Tag.Index))}
    (state : State ctx (Tag.prod Reference) H) (update : Store ctx × H → Store ctx × K) :
    decodeReferenceTag
        (@ExecutionState.mapClassical _ _ _ _ _ beforeMap state update) =
      @ExecutionState.mapClassical _ _ _ _ _ afterMap (decodeReferenceTag state)
        (fun record =>
          let result := update (record.1, record.2.1)
          (result.1, (result.2, record.2.2))) := by
  refine Eq.trans ?_ ((decodeReferenceTag_mapRecord state update).trans ?_)
  · exact congrArg
      (fun current : State ctx (Tag.prod Reference) K => decodeReferenceTag current)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- A sampled store update preserves every complete tag slice and its actual probability. -/
lemma decodeReferenceTag_kernelRecord
    (state : State ctx (Tag.prod Reference) H)
    (transition : Store ctx × H → PMF Outcome)
    (update : (Store ctx × H) × Outcome → Store ctx × K) :
    decodeReferenceTag ((kernelChoice state transition).mapClassical update) =
      (kernelChoice (decodeReferenceTag state)
        (fun record => transition (record.1, record.2.1))).mapClassical (fun record =>
          let result := update ((record.1.1, record.1.2.1), record.2)
          (result.1, (result.2, record.1.2.2))) := by
  have reassociated : (kernelChoice state transition).mapClassical update =
      (kernelOutcome state transition).mapClassical
        (fun record => update ((record.1, record.2.1), record.2.2)) := by
    simp only [kernelOutcome, ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  rw [reassociated, decodeReferenceTag_mapRecord, decodeReferenceTag_kernelOutcome]
  simp only [mapHistory, kernelOutcome, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Sampled tag slices are independent of the record equality-decision implementations. -/
lemma decodeReferenceTag_kernelRecord_decisions
    {beforeMap : DecidableEq (Store ctx × K)}
    {afterMap : DecidableEq (Store ctx × (K × Tag.Index))}
    (state : State ctx (Tag.prod Reference) H)
    (transition : Store ctx × H → PMF Outcome)
    (update : (Store ctx × H) × Outcome → Store ctx × K) :
    decodeReferenceTag
        (@ExecutionState.mapClassical _ _ _ _ _ beforeMap
          (kernelChoice state transition) update) =
      @ExecutionState.mapClassical _ _ _ _ _ afterMap
        (kernelChoice (decodeReferenceTag state)
          (fun record => transition (record.1, record.2.1))) (fun record =>
            let result := update ((record.1.1, record.1.2.1), record.2)
            (result.1, (result.2, record.1.2.2))) := by
  refine Eq.trans ?_ ((decodeReferenceTag_kernelRecord state transition update).trans ?_)
  · exact congrArg
      (fun current : State ctx (Tag.prod Reference) K => decodeReferenceTag current)
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- A measurement write retains the complete selected tag slice and the actual readout. -/
lemma decodeReferenceTag_measureRecord
    (state : State ctx (Tag.prod Reference) H)
    (readout : ctx.register.Index → Outcome)
    (update : (Store ctx × H) × Outcome → Store ctx × K) :
    decodeReferenceTag
        ((ExecutionState.measureZ state (fun basis => readout basis.1)).mapClassical update) =
      (ExecutionState.measureZ (decodeReferenceTag state)
        (fun basis => readout basis.1)).mapClassical (fun record =>
          let result := update ((record.1.1, record.1.2.1), record.2)
          (result.1, (result.2, record.1.2.2))) := by
  have reassociated :
      (ExecutionState.measureZ state (fun basis => readout basis.1)).mapClassical update =
        (measureOutcome state readout).mapClassical
          (fun record => update ((record.1, record.2.1), record.2.2)) := by
    simp only [measureOutcome, ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  rw [reassociated, decodeReferenceTag_mapRecord, decodeReferenceTag_measureOutcome]
  simp only [mapHistory, measureOutcome, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Measurement tag slices are independent of outcome and record equality decisions. -/
lemma decodeReferenceTag_measureRecord_decisions
    {outcomeDecision : DecidableEq Outcome} {beforeMap : DecidableEq (Store ctx × K)}
    {afterMap : DecidableEq (Store ctx × (K × Tag.Index))}
    (state : State ctx (Tag.prod Reference) H)
    (readout : ctx.register.Index → Outcome)
    (update : (Store ctx × H) × Outcome → Store ctx × K) :
    decodeReferenceTag
        (@ExecutionState.mapClassical _ _ _ _ _ beforeMap
          (@ExecutionState.measureZ (Store ctx × H) Outcome _ _
            (ctx.register.prod (Tag.prod Reference)) outcomeDecision state
              (fun basis => readout basis.1)) update) =
      @ExecutionState.mapClassical _ _ _ _ _ afterMap
        (@ExecutionState.measureZ (Store ctx × (H × Tag.Index)) Outcome _ _
          (ctx.register.prod Reference) outcomeDecision (decodeReferenceTag state)
            (fun basis => readout basis.1)) (fun record =>
              let result := update ((record.1.1, record.1.2.1), record.2)
              (result.1, (result.2, record.1.2.2))) := by
  cases Subsingleton.elim outcomeDecision (Classical.decEq Outcome)
  refine Eq.trans ?_ ((decodeReferenceTag_measureRecord state readout update).trans ?_)
  · exact congrArg
      (fun current : State ctx (Tag.prod Reference) K => decodeReferenceTag current)
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Execution.State
