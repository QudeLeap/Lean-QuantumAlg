/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Resources
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Time

/-!
# Independent bounds for the simultaneous bank reset

The existing native envelope still bounds the same actual measurement and
selected X events. Its weighted total is a coarse bound for arbitrary event
durations. Canonical quantum time instead follows the real single correction
layer, and the empty bank has zero time and no scratch allocation.
-/

namespace QuantumAlg.ZReset.BankParallel

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)

/-- The original independent native envelope includes every actual simultaneous reset event. -/
lemma code_eventEnvelope_le
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).resourcePool path ≤
      Bank.envelope (oracles := oracles) ctx.systemCount operations services := by
  simpa only [Bank.envelope, eventEnvelope, nsmul_add] using code_resourcePool_le qubits path

/-- Total native work gives a conservative unit-duration critical-path bound. -/
lemma code_unitDepth_le
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).depth (fun _ => 1) path ≤
      2 * ctx.systemCount := by
  refine (Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1)
    (Bank.envelope (oracles := oracles) ctx.systemCount operations services)
    path (code_eventEnvelope_le qubits path)).trans_eq ?_
  simp only [Bank.envelope, eventEnvelope, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton, Nat.one_mul]
  omega

/-- Every recorded event is one actual measurement or one selected X. -/
lemma code_eventTrace_length_le
    (path : (code (oracles := oracles) qubits operations services).Path) :
    ((code (oracles := oracles) qubits operations services).eventTrace path).length ≤
      2 * ctx.systemCount := by
  have repeated (count : Nat)
      (pool : ResourcePool (.quantum AlgorithmGate.model oracles operations services)) :
      Multiset.card (count • pool) = count * Multiset.card pool := by
    induction count with
    | zero => simp only [zero_nsmul, zero_mul, Multiset.card_zero]
    | succ count ih => simp only [succ_nsmul, Multiset.card_add, ih, Nat.succ_mul]
  have bounded := Multiset.card_le_card (code_resourcePool_le qubits path)
  simpa only [Circuit.resourcePool, ResourcePool.ofList, ResourcePool.singleton,
    Multiset.card_add, repeated, Multiset.card_replicate,
    Nat.mul_one, Multiset.coe_card, two_mul] using bounded

/-- The real correction layer has time at most one, with literal zero time at width zero. -/
lemma code_quantumTime_le_layer
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).quantumTime path ≤
      if ctx.systemCount = 0 then 0 else 1 := by
  by_cases empty : ctx.systemCount = 0
  · revert path
    rw [code_zero qubits empty]
    intro path
    simp only [Circuit.quantumTime_id, empty, if_true, Nat.le_refl]
  · simpa only [empty, if_false] using code_quantumTime_le qubits path

end

end QuantumAlg.ZReset.BankParallel
