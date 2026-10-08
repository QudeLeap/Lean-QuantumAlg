/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.State
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Reference-aware observations of an actual EH batch slot write

The second paid pack writes one actual retained result slot. A separated old
read keeps its complete weighted reference matrix, including off-diagonal
reference entries and correlations with all previous batch samples.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual copy transports any store-weighted reference observation
through precisely its real classical write. -/
theorem copy_reference (index : Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : Store (context base noQuantum N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((copy base noQuantum N input index).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (copyStep base noQuantum N input index entry.1).1)
      leftRef rightRef := by
  rw [copy_execute]
  simp only [ExecutionState.referenceFiberSum_mapClassical]

/-- Any structural read outside the written slot retains every reference
matrix coefficient through the paid copy. -/
theorem copy_frame_reference {shape : CShape} (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (separate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : shape.Value → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((copy base noQuantum N input index).execute Reference state)
      (fun entry _ => weight (entry.1.read observed)) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (entry.1.read observed)) leftRef rightRef := by
  refine (copy_reference base noQuantum N input index state
    (fun store => weight (store.read observed)) leftRef rightRef).trans ?_
  simp only [copy_frame base noQuantum N input index observed separate]

/-- The paid copy combines a preserved old read with the outcome encoded by
the actual measured cells, retaining every reference matrix coefficient. -/
theorem copy_joint_reference {shape : CShape} (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (separate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((copy base noQuantum N input index).execute Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (entry.1.read observed) *
        (if copiedValue base noQuantum N entry.1 = CShape.Value.bits outcome
          then 1 else 0)) leftRef rightRef := by
  refine (copy_reference base noQuantum N input index state
    (fun store => weight (store.read observed) *
      (if store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef).trans ?_
  apply congrArg
    (fun read : (Store (context base noQuantum N) ×
        ((model input).HiddenState × History)) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state read leftRef rightRef)
  funext entry basis
  rw [copy_frame base noQuantum N input index observed separate entry.1,
    copy_read base noQuantum N input index entry.1]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
