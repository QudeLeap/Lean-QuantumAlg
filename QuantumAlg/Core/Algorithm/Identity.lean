/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

import all QuantumAlg.Core.Execution.Input.Successor.Sequence
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# The identity algorithm and its independent complete contract

The identity preserves its entire live context and incurs zero quantum time.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
  {shape : CShape} (read : OutputRead ctx shape)

/-- An independent, payload-free contract for an unchanged context. -/
def identityProblem :
    Problem model ctx ctx shape where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨0, zero_le_one⟩
  states := fun _ _ => []
  resources :=
    { events := 0
      resident := ctx.residentSpace
      auxiliary := ctx.auxiliarySpace }
  quantumTimeLimit := 0

/-- The complete live identity run observes only the unit payload. -/
def identityAlgorithm : Algorithm model ctx ctx shape where
  run := { code := .id ctx, output := Output.all ctx read }

/-- The real identity circuit meets its independent zero-event contract. -/
lemma identityAlgorithm_solves :
    Algorithm.Solves (identityAlgorithm (model := model) ctx read)
      (identityProblem (shape := shape) ctx) := by
  constructor
  · intro _environment _witness _ _ _ _
    exact zero_le
  · intro _environment _witness _ _ _ _ _ present
    exact False.elim (List.not_mem_nil present)
  · intro environment _witness _ _ _ _
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro Reference History _ state
    exact borrowedRestored_id environment state
  · intro _environment _witness _ _ _ _ path _
    change ResourcePool.ofList ([] : List (Resource.Event model)) ≤ 0
    rfl
  · intro _environment _witness _ _ _ _ path _
    change (Circuit.id (model := model) ctx).Path at path
    change (Circuit.id (model := model) ctx).peakResidentSpace path ≤ ctx.residentSpace
    exact le_of_eq (peakResidentSpace_id path)
  · intro _environment _witness _ _ _ _ path _
    change (Circuit.id (model := model) ctx).Path at path
    change (Circuit.id (model := model) ctx).peakAuxiliarySpace path ≤ ctx.auxiliarySpace
    exact le_of_eq (peakAuxiliarySpace_id path)
  · intro _environment _witness _ _ _ _ path _
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    change 0 ≤ 0
    exact le_refl _

end

end QuantumAlg.Circuit
