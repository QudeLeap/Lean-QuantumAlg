/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Complete events and chronological depth of the actual finite declared tail

Every requested iteration pays the full sampler, selected query and native
peripherals, measured readout and bit packing, complete factor recovery and
first-success feedback, then physical bank reset. The optional output is
materialized exactly once after the real finite body. Neither the event
allowance nor the duration-dependent depth limit comes from an execution path.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

/-- Every complete round contributes once, followed by the sole paid output encoding. -/
def eventEnvelope (N : Nat) (count : Nat) :
    ResourcePool (executionModel N) :=
  ResourcePool.scale count (completionEnvelope N) +
    ResourcePool.singleton (model := executionModel N)
      (.classicalOperation (BitWord.selectedCoordinate (execution := executionModel N)
        (.nominalEncoding (.packOption (modulusBits N)))))

/-- All real chronological rounds fit the independent multiplicity of the full one-round ledger. -/
lemma body_pool_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (count : Nat)
    (path : (body ctx N input sameWires cells result count).Path) :
    (body ctx N input sameWires cells result count).resourcePool path ≤
      ResourcePool.scale count (completionEnvelope N) := by
  induction count generalizing ctx with
  | zero => exact le_rfl
  | succ count induction =>
      rcases path with ⟨firstPath, restPath⟩
      change ResourcePool.ofList
        ((Completion.code ctx N input sameWires cells result).eventTrace firstPath ++
          (body (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)
            (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) count).eventTrace
              restPath) ≤ _
      rw [ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (Completion.code_pool_le ctx N input sameWires cells result firstPath)
        (induction (Iteration.context ctx N) ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) restPath)

/-- The complete actual tail pays its one final pack after all requested full rounds. -/
lemma code_pool_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code ctx N input sameWires count cells result).Path) :
    (code ctx N input sameWires count cells result).resourcePool path ≤
      eventEnvelope N count := by
  rcases path with ⟨roundsPath, packedPath⟩
  change ResourcePool.ofList
    ((body ctx N input sameWires cells result count).eventTrace roundsPath ++
      (pack ctx N count cells result).eventTrace packedPath) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (body_pool_le ctx N input sameWires cells result count roundsPath) le_rfl

/-- The chronological depth remains that of the whole actual tail under the chosen durations. -/
lemma code_depth_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (duration : Resource.Event (executionModel N) → Nat)
    (path : (code ctx N input sameWires count cells result).Path) :
    (code ctx N input sameWires count cells result).depth duration path ≤
      ResourcePool.weightedCount duration (eventEnvelope N count) :=
  Circuit.depth_le_weightedCount_of_pool_le (code ctx N input sameWires count cells result)
    duration (eventEnvelope N count) path
    (code_pool_le ctx N input sameWires count cells result path)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
