/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Resources
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Initialization and complete first-round event ledgers

The five genuine retained heads require no arithmetic instruction. The real
latch clear pays one XOR, and every actual bank wire pays its own preparation
event. The first complete cycle then pays the entire sampling, recovery,
feedback and physical reset allowance. These independent formulas never
inspect an execution path or a fixed arithmetic instance.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- One real latch clear and one dimension-two preparation per physical bank wire. -/
def readyEnvelope (N : Nat) : ResourcePool (executionModel N) :=
  ResourcePool.singleton (.classicalOperation
    (BitWord.selectedCoordinate (execution := executionModel N) (.bit .xor))) +
      (bankQubits N) • ResourcePool.singleton (model := executionModel N)
        (.preparation (2 : ℕ+))

/-- A complete first cycle includes the actual initializer and complete first attempt. -/
def firstEnvelope (N : Nat) : ResourcePool (executionModel N) :=
  readyEnvelope N + completionEnvelope N

/-- Actual storage allocation and physical preparation have precisely the independent ledger. -/
lemma ready_pool_eq (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (path : (ready base noQuantum N).Path) :
    (ready base noQuantum N).resourcePool path = readyEnvelope N := by
  change ResourcePool.ofList
    ([.classicalOperation (.bit .xor)] ++ ZeroPreparation.eventTrace AlgorithmGate.model
      (DeclaredSource.model (modulusBits N) (phaseBits N)) (layout N) BitWord.model .empty) = _
  rw [ResourcePool.ofList_append]
  change ResourcePool.singleton (model := executionModel N)
    (.classicalOperation (.bit .xor)) +
    ZeroPreparation.eventCost AlgorithmGate.model
      (DeclaredSource.model (modulusBits N) (phaseBits N)) (layout N) BitWord.model .empty = _
  rw [ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (DeclaredSource.model (modulusBits N) (phaseBits N)) (layout N) 2
      (fun _ => rfl) BitWord.model ClassicalOracleModel.empty]
  rfl

/-- Every actual first-round path pays initialization and the complete actual round. -/
lemma code_pool_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).resourcePool path ≤ firstEnvelope N := by
  rcases path with ⟨readyPath, roundPath⟩
  change ResourcePool.ofList ((ready base noQuantum N).eventTrace readyPath ++
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N)).eventTrace roundPath) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (ready_pool_eq base noQuantum N readyPath).le
    (Completion.code_pool_le (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N) roundPath)

/-- Dependency depth bounds the complete real first cycle, including its physical preparation. -/
lemma code_depth_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (duration : Resource.Event (executionModel N) → Nat)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).depth duration path ≤
      ResourcePool.weightedCount duration (firstEnvelope N) :=
  Circuit.depth_le_weightedCount_of_pool_le (code base noQuantum N input) duration
    (firstEnvelope N) path (code_pool_le base noQuantum N input path)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
