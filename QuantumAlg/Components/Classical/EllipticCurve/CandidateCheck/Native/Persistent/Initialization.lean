/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Semantics
import all QuantumAlg.Core.Execution.State.Effect
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Actual initial persistent acceptance and selected values

The original seven retain instructions initialize their real latches. Their
complete state record yields the initial positive-block support and the full
subnormalized failure mass without a caller initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

private lemma mapped_indicator_weight {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (decision : DecidableEq D) (state : ExecutionState C R) (update : C → D)
    (condition : D → Prop) [DecidablePred condition] :
    (@ExecutionState.mapClassical C D _ _ R decision state update).effectWeight
        (fun entry => if condition entry then Effect.one R else Effect.zero R) =
      state.effectWeight
        (fun entry => if condition (update entry) then Effect.one R else Effect.zero R) := by
  classical
  exact ExecutionState.effectWeight_mapClassical_decision decision state update _

private lemma mapped_record_positive {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (decision : DecidableEq D) (state : ExecutionState C R) (update : C → D) (value : D) :
    0 < ((@ExecutionState.mapClassical C D _ _ R decision state update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  cases Subsingleton.elim decision (Classical.decEq D)
  exact ExecutionState.mapClassical_block_mass_pos_iff state update value

private lemma allocation_latches (width scalarWidth : Nat) (before : Store ctx) :
    ((persistentAllocationStep (model := model) width scalarWidth before).1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false ∧
    (persistentAllocationStep (model := model) width scalarWidth before).1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        CShape.initialValue (.unsignedWord scalarWidth) := by
  exact ⟨congrArg CShape.Value.toBool
    (persistentInitialStore_accepted width scalarWidth before),
      persistentInitialStore_selected width scalarWidth before⟩

/-- Every positive actual allocation block has the original initial first-success latches. -/
lemma retainPersistent_latches_supported (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (retainPersistent ctx width scalarWidth).Path)))
    (positive : 0 < (((retainPersistent ctx width scalarWidth).execute environment
      Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        false ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        CShape.initialValue (.unsignedWord scalarWidth) := by
  rw [retainPersistent_execute] at positive
  unfold persistentAllocationState at positive
  obtain ⟨original, equality, _⟩ := (mapped_record_positive _ state
    (fun entry => ((persistentAllocationStep width scalarWidth entry.1).1,
      (entry.2.1, (entry.2.2,
        (persistentAllocationStep width scalarWidth entry.1).2)))) result).mp positive
  rw [← equality]
  exact allocation_latches width scalarWidth original.1

/-- Real allocation starts with failure mass equal to all incoming subnormalized mass. -/
lemma retainPersistent_failure_weight (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H)) :
    ((retainPersistent ctx width scalarWidth).execute environment Reference state).effectWeight
        (fun entry => if (entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
            Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
          else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      state.mass := by
  rw [retainPersistent_execute]
  unfold persistentAllocationState
  refine (mapped_indicator_weight _ state
    (fun entry => ((persistentAllocationStep width scalarWidth entry.1).1,
      (entry.2.1, (entry.2.2,
        (persistentAllocationStep width scalarWidth entry.1).2))))
    (fun entry => (entry.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false)).trans ?_
  unfold ExecutionState.effectWeight ExecutionState.mass
  apply Finset.sum_congr rfl
  intro entry _
  dsimp only
  rw [(allocation_latches width scalarWidth entry.1).1, if_pos rfl, Effect.weight_one]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
