/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Resources
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Exact resources of the genuine zero-round Shor execution

The machine still clears its latch, prepares the real bank and executes its
terminal optional-result pack. The two classical instructions are actual
events of the same path, including when no sampling attempt is requested.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

noncomputable section

/-- The zero-round path has exactly its complete initialization and terminal-pack envelope. -/
lemma zero_pool_eq (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (path : (code base noQuantum N input 0).Path) :
    (code base noQuantum N input 0).resourcePool path = eventEnvelope N 0 := by
  change ResourcePool.ofList ((Initialized.ready base noQuantum N).eventTrace path.1 ++
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) 0
      (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)).eventTrace
        path.2) = _
  rw [ResourcePool.ofList_append]
  change (Initialized.ready base noQuantum N).resourcePool path.1 + _ = _
  rw [Initialized.ready_pool_eq]
  rfl

/-- Exactly two classical operations execute even when there are no sampling attempts. -/
lemma zero_classical_operations (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    (path : (code base noQuantum N input 0).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code base noQuantum N input 0).resourcePool path) = 2 := by
  rw [zero_pool_eq]
  simp [eventEnvelope, Initialized.readyEnvelope, Finite.eventEnvelope, ResourcePool.scale,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
