/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# The terminal identity section of an actual finite circuit range

`Circuit.forRange 0` is the real identity circuit. A schedule may account for
this harmless terminal section as classical work without inventing a quantum
cycle or omitting its unchanged live context.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
  {shape : CShape} (read : OutputRead ctx shape)

/-- An independent, payload-free contract for an unchanged context. -/
def identityProblem (duration : Resource.Event model → Nat)
    (classicalQuery_unit : ∀ coordinate, duration (.classicalQuery coordinate) = 1)
    (quantumQuery_unit : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem model ctx ctx shape where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨0, zero_le_one⟩
  states := []
  resources :=
    { events := 0
      resident := ctx.residentSpace
      auxiliary := ctx.auxiliarySpace }
  depth :=
    { duration := duration
      limit := 0
      classicalQuery_unit := classicalQuery_unit
      quantumQuery_unit := quantumQuery_unit }

/-- The complete live identity run observes only the unit payload. -/
def identityAlgorithm : Algorithm model ctx ctx shape where
  run := { code := .id ctx, output := Output.all ctx read }

/-- The real identity circuit meets its independent zero-event contract. -/
theorem identityAlgorithm_solves (duration : Resource.Event model → Nat)
    (classicalQuery_unit : ∀ coordinate, duration (.classicalQuery coordinate) = 1)
    (quantumQuery_unit : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.Solves (identityAlgorithm (model := model) ctx read)
      (identityProblem (shape := shape) ctx duration
        classicalQuery_unit quantumQuery_unit) := by
  constructor
  · intro _ _ _ _
    exact zero_le
  · intro _ _ _ _ _ present
    exact False.elim (List.not_mem_nil present)
  · intro _ _ _ _
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro Reference History _ state
    exact borrowedRestored_id state
  · intro _ _ _ _ path _
    change ResourcePool.ofList ([] : List (Resource.Event model)) ≤ 0
    rfl
  · intro _ _ _ _ path _
    change (Circuit.id (model := model) ctx).Path at path
    change (Circuit.id (model := model) ctx).peakResidentSpace path ≤ ctx.residentSpace
    exact le_of_eq (peakResidentSpace_id path)
  · intro _ _ _ _ path _
    change (Circuit.id (model := model) ctx).Path at path
    change (Circuit.id (model := model) ctx).peakAuxiliarySpace path ≤ ctx.auxiliarySpace
    exact le_of_eq (peakAuxiliarySpace_id path)
  · intro _ _ _ _ path _
    change 0 ≤ 0
    exact le_refl _

/-- The terminal range identity contains no event, so is strictly classical. -/
theorem identityClassical : IsClassical (Circuit.id (model := model) ctx) := by
  intro _ _ present
  exact False.elim (List.not_mem_nil present)

/-- The terminal identity contributes only an erased history marker. Its
actual successor input has precisely the same joint caller/service state. -/
theorem nextInput_seq_identity_state {pre : RuntimeCtx model.kind}
    (code : Circuit model pre ctx) {Reference : Register}
    (original : Execution.OracleInput model.classicalOracles pre Reference) :
    ((code.seq (Circuit.id (model := model) ctx)).nextInput original).state =
      (code.nextInput original).state := by
  change
    (((code.seq (Circuit.id (model := model) ctx)).execute Reference
      (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
        (fun record => (record.1, record.2.1))) =
    ((code.execute Reference
      (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
        (fun record => (record.1, record.2.1)))
  rw [execute_seq, execute_id_mapClassical]
  dsimp only [Execution.State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq _),
    ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq _)]
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
    (fun _ => rfl) _ _

/-- Explicit classical schedule for the actual zero-length range tail. -/
def identitySchedule (duration : Resource.Event model → Nat)
    (classicalQuery_unit : ∀ coordinate, duration (.classicalQuery coordinate) = 1)
    (quantumQuery_unit : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleSchedule
      (.classical (identityProblem (shape := shape) ctx duration
        classicalQuery_unit quantumQuery_unit))
      (Circuit.id (model := model) ctx) :=
  .classical _
    { output := (identityAlgorithm (model := model) ctx read).run.output
      certified := identityAlgorithm_solves ctx read duration
        classicalQuery_unit quantumQuery_unit }
    (identityClassical ctx)

end

end QuantumAlg.Circuit
