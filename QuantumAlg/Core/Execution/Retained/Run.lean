/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Retained.Record

/-!
# Complete run records after an actual retained continuation

The proposition below is the existing AlgorithmRun execution equation with
an actual deterministic record map. It keeps every final store block, the
initial classical history, both execution paths and the arbitrary external
reference. Its generic composition theorem follows from the actual retained
circuit record. Complete Output manifests remain part of both real runs.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre middle : RuntimeCtx model.kind}
  {key : StorageKey} {shape sourceShape resultShape : CShape} {fresh : key ∉ middle.keys}

/-- Actual complete execution records are mapped with all quantum-reference blocks intact. -/
def RetainedRecord (source : AlgorithmRun model pre middle sourceShape)
    (result : AlgorithmRun model pre (middle.addRetained key shape fresh) resultShape)
    (environment : model.Environment)
    (update : source.Record → result.Record) : Prop :=
  ∀ (Reference : Register)
    (input : ExecutionState (Store pre × model.HiddenState) (Register.prod pre.register Reference)),
    result.execute environment Reference input =
      (source.execute environment Reference input).mapClassical (D := result.Record) update

/-- A real retained circuit record composes with any complete source run and output manifest. -/
lemma RetainedRecord.ofTail (source : AlgorithmRun model pre middle sourceShape)
    (tail : Circuit model middle (middle.addRetained key shape fresh))
    (environment : model.Environment)
    (output : Output (middle.addRetained key shape fresh) resultShape)
    (step : Store middle × model.HiddenState →
      (Store (middle.addRetained key shape fresh) × model.HiddenState) × tail.Path)
    (record : Circuit.RetainedRecord tail environment step) :
    RetainedRecord source { code := .seq source.code tail, output := output } environment
      (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2.1, (entry.2.2.2, result.2))))) := by
  intro Reference input
  unfold execute
  exact (Circuit.RetainedRecord.after source.code tail environment step record Reference
    (input.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)

end

end QuantumAlg.AlgorithmRun
