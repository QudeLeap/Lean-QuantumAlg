/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.State

/-!
# Complete execution transport for a quantum circuit's classical grants

The source and target have the same quantum gates, quantum oracles and empty
classical oracle service. A selected classical operation language may extend
the target, but a certificate must preserve every weighted execution block.
Its path equivalence reindexes only the mathematical execution history; the
store, hidden service state, quantum system and arbitrary reference remain in
the same complete state.
-/

namespace QuantumAlg.Circuit

noncomputable section

/-- Relabel a mathematical path without changing any weighted quantum block. -/
public def relabelPath {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {Hidden H P Q : Type}
    [Fintype Hidden] [Fintype H] [Fintype P] [Fintype Q]
    (state : Execution.State ctx Reference (Hidden × (H × P))) (paths : P → Q) :
    Execution.State ctx Reference (Hidden × (H × Q)) := by
  classical
  exact state.mapClassical (fun record =>
    (record.1, (record.2.1, (record.2.2.1, paths record.2.2.2))))

/-- A concrete classical-grant selection certified on complete execution states. -/
public structure QuantumClassicalSelection {gates : GateModel} {oracles : OracleModel}
    (operations : ClassicalOpModel) {allowAllocation : Bool}
    {pre post : RuntimeCtx .quantum}
    (source : Circuit (.quantum gates oracles) pre post allowAllocation) where
  /-- The selected code keeps the original quantum gate and oracle models. -/
  code : Circuit (.quantum gates oracles operations) pre post allowAllocation
  /-- Every actual source path has one selected path and conversely. -/
  paths : source.Path ≃ code.Path
  /-- The complete output state differs only by reindexing the path history. -/
  execute : ∀ (environment : oracles.Interpretation) (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference
      ((.quantum gates oracles : ExecutionModel).HiddenState × H)),
    code.execute ⟨environment, ()⟩ Reference state =
      relabelPath (source.execute ⟨environment, ()⟩ Reference state) paths

end

end QuantumAlg.Circuit
