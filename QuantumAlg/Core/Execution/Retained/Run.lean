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

variable {kind : ProblemKind} {pre middle : RuntimeCtx kind}
  {key : StorageKey} {shape sourceShape resultShape : CShape} {fresh : key ∉ middle.keys}

/-- Actual complete execution records are mapped with all quantum-reference blocks intact. -/
def RetainedRecord (source : AlgorithmRun pre middle sourceShape)
    (result : AlgorithmRun pre (middle.addRetained key shape fresh) resultShape)
    (update : source.Record → result.Record) : Prop :=
  ∀ (Reference : Register)
    (input : ExecutionState (Store pre) (Register.prod pre.register Reference)),
    result.execute Reference input =
      (source.execute Reference input).mapClassical (D := result.Record) update

/-- A real retained circuit record composes with any complete source run and output manifest. -/
theorem RetainedRecord.ofTail (source : AlgorithmRun pre middle sourceShape)
    (tail : Circuit middle (middle.addRetained key shape fresh))
    (output : Output (middle.addRetained key shape fresh) resultShape)
    (step : Store middle → Store (middle.addRetained key shape fresh) × tail.Path)
    (record : Circuit.RetainedRecord tail step) :
    RetainedRecord source { code := .seq source.code tail, output := output }
      (fun entry => ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2)))) := by
  intro Reference input
  unfold execute
  refine (Circuit.RetainedRecord.after source.code tail step record Reference
    (input.mapClassical (fun store => (store, store)))).trans ?_
  let normalize := fun decision => Circuit.mapClassical_canonicalDecision decision
    (source.code.execute Reference (input.mapClassical (fun store => (store, store))))
    (fun entry => ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))
  exact (normalize _).trans (normalize _).symm

end

end QuantumAlg.AlgorithmRun
