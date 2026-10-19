/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Frame
import all QuantumAlg.Core.Execution.Random.Observation
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Uniform redraw jointly with all earlier EH sample data

The source draw has one shared uniform value. It overwrites only the source
and derived parameter, retaining a separated old read, the quantum bank,
the hidden service state and every reference matrix coefficient.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma liftedSamples_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (width : Nat) (ref : CWriteRef ctx shape) (count : Nat) :
    (Native.Batch.Slots.liftSamples width ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private lemma parameter_source_ne :
    (parameterRef base noQuantum N).key ≠
      (sourceRef base noQuantum N).key := by
  intro same
  have parameterKey := (underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))).trans
      (liftedSamples_key (measurementBits N)
        (ShorStyle.Canonical.Sampler.Retained.parameterRef base N) 16)
  have sourceKey := (underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))).trans
      (liftedSamples_key (measurementBits N)
        (ShorStyle.Canonical.Sampler.Retained.sampleRef base N) 16)
  exact ShorStyle.Canonical.Sampler.Retained.samplerRetained_parameter_key_ne_sample base N
    ((parameterKey.symm.trans same).trans sourceKey)

private lemma redraw_weight (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N))
    (weight : (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ) :
    weight ((redrawStep base noQuantum N store value).1.read
        (.storage (parameterRef base noQuantum N).toCStorageRef))
      ((redrawStep base noQuantum N store value).1.read
        (.storage (sourceRef base noQuantum N).toCStorageRef)) =
      weight (parameterValue input value)
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) := by
  have actual := congrArg (fun result : Store (context base noQuantum N) =>
    weight (result.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (result.read (.storage (sourceRef base noQuantum N).toCStorageRef)))
    (redraw_store base noQuantum N input store value)
  refine actual.trans ?_
  apply congrArg₂ weight
  · exact Store.read_write_same _ _ _
  · exact (Store.read_write_other _ (parameterRef base noQuantum N)
      (sourceRef base noQuantum N).toCStorageRef _
      (parameter_source_ne base noQuantum N)).trans
        (Store.read_write_same _ _ _)

set_option maxHeartbeats 1000000 in
-- The state carries the full bank and reference; aligning its two execution views
-- requires more reduction than the default per-declaration heartbeat budget.
/-- The actual uniform redraw has one common new parameter and source while
preserving any separated old value and the entire external reference. -/
lemma redraw_frame_reference {shape : CShape}
    (observed : CInputRef (context base noQuantum N) shape)
    (separated : RedrawSeparated base noQuantum N observed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((redraw base noQuantum N).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (entry.1.read observed)
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)))
      leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          weight (entry.1.read observed) (parameterValue input value)
            (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
      leftRef rightRef := by
  classical
  let count : ℕ+ := ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
  let update := fun entry :
      (Store (context base noQuantum N) × ((model N).HiddenState × History)) ×
        Fin count =>
    ((redrawStep base noQuantum N entry.1.1 entry.2).1,
      (entry.1.2.1, (entry.1.2.2,
        (redrawStep base noQuantum N entry.1.1 entry.2).2)))
  let observe := fun store : Store (context base noQuantum N) =>
    weight (store.read observed)
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
      ((model N).HiddenState ×
        (History × (redraw base noQuantum N).Path)) =>
      ExecutionState.referenceFiberSum output
        (fun entry _ => observe entry.1) leftRef rightRef)
    (redraw_execute (environment := sourceEnvironment input) base noQuantum N Reference state)
  have pushed := ExecutionState.referenceFiberSum_mapClassical
    (decision := inferInstance)
    (uniformChoice state count) update
    (fun entry _ => observe entry.1) leftRef rightRef
  have sampled := referenceFiberSum_uniformChoice state count
    (fun entry _ => observe (update entry).1) leftRef rightRef
  have coefficient : (((count : ℝ)⁻¹ : ℝ) : ℂ) =
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) := by
    rw [Complex.ofReal_inv]
    exact congrArg (fun number : ℝ => (number : ℂ)⁻¹)
      (show (count : ℝ) = ((2 ^ residueSamplingBits N : Nat) : ℝ) from rfl)
  have alignedState :
      ((uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => ((redrawStep base noQuantum N entry.1.1 entry.2).1,
          (entry.1.2.1, (entry.1.2.2,
            (redrawStep base noQuantum N entry.1.1 entry.2).2))))) =
      (uniformChoice state count).mapClassical update := by
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  have aligned := congrArg
    (fun output : State (context base noQuantum N) Reference
      ((model N).HiddenState ×
        (History × (redraw base noQuantum N).Path)) =>
      ExecutionState.referenceFiberSum output
        (fun entry _ => observe entry.1) leftRef rightRef) alignedState
  calc
    _ = ExecutionState.referenceFiberSum
        ((uniformChoice state count).mapClassical update)
        (fun entry _ => observe entry.1) leftRef rightRef := executed.trans aligned
    _ = ExecutionState.referenceFiberSum (uniformChoice state count)
        (fun entry _ => observe (update entry).1) leftRef rightRef := pushed
    _ = ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin count,
          (((count : ℝ)⁻¹ : ℝ) : ℂ) * observe (update (entry, value)).1)
        leftRef rightRef := sampled
    _ = _ := by
      apply congrArg
        (fun read : (Store (context base noQuantum N) ×
            ((model N).HiddenState × History)) →
            (context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum state read leftRef rightRef)
      funext entry basis
      apply Finset.sum_congr rfl
      intro value _
      apply congrArg₂ HMul.hMul coefficient
      dsimp only [observe, update]
      refine (congrArg (fun old => weight old _ _)
        (redraw_frame_read base noQuantum N input observed separated entry.1 value)).trans ?_
      exact redraw_weight base noQuantum N input entry.1 value
        (weight (entry.1.read observed))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
