/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration.Resources

/-!
# Actual native resource bounds for the finite same-bank sampling batch

Induction follows the real context-changing sequence of sampled rounds. Every
round keeps its actual classical results while using the same bank and complete
reset/reload suffix. The enclosing prepared batch charges its one real basis
preparation separately. All formulas depend only on the public modulus and the
actual finite iteration count, and include the zero-round case.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

namespace NativeBatch

/-- Independent finite multiplicity of the complete sampled-round native allowance. -/
def eventEnvelope (N count : Nat) : ResourcePool .quantum :=
  ResourcePool.scale count (NativeIteration.eventEnvelope N)

/-- Independent serial sum of all complete sampled rounds. -/
def depthBound (N count : Nat) : Nat := count * NativeIteration.depthBound N

/-- The real context-changing iteration obeys the independent finite native event envelope. -/
theorem code_pool_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    (path : (code ctx N sameWires count).Path) :
    (code ctx N sameWires count).resourcePool path ≤ eventEnvelope N count := by
  induction count generalizing ctx with
  | zero => exact (ResourcePool.scale_zero _).symm.le
  | succ count induction =>
      change ResourcePool.ofList ((NativeIteration.code ctx N sameWires).eventTrace path.1 ++
        (code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      change _ ≤ ResourcePool.scale (count + 1) (NativeIteration.eventEnvelope N)
      rw [ResourcePool.scale_succ]
      exact add_le_add (NativeIteration.code_pool_le ctx N sameWires path.1)
        (induction (NativeIteration.context ctx N)
          ((NativeIteration.quantumWires ctx N).trans sameWires) path.2)

/-- Every actual round's sampled and quantum serial dependencies remain in the full finite sum. -/
theorem code_unitDepth_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    (path : (code ctx N sameWires count).Path) :
    (code ctx N sameWires count).depth (fun _ => 1) path ≤ depthBound N count := by
  induction count generalizing ctx with
  | zero => exact Nat.zero_le _
  | succ count induction =>
      have first := NativeIteration.code_unitDepth_le ctx N sameWires path.1
      have later := induction (NativeIteration.context ctx N)
        ((NativeIteration.quantumWires ctx N).trans sameWires) path.2
      change (NativeIteration.code ctx N sameWires).depth (fun _ => 1) path.1 +
        (code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count).depth
            (fun _ => 1) path.2 ≤ _
      unfold depthBound at later ⊢
      rw [Nat.succ_mul]
      omega

end NativeBatch

namespace NativePreparedBatch

/-- Exactly one fixed source-seed preparation prefixes the independent finite batch budget. -/
def eventEnvelope (N count : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (NativeQuantum.seedPreparation N).event + NativeBatch.eventEnvelope N count

/-- One real preparation precedes the serial sum of complete sampled rounds. -/
def depthBound (N count : Nat) : Nat := 1 + NativeBatch.depthBound N count

/-- The actual single prepared bank and all real sampling rounds fit the full event allowance. -/
theorem code_pool_le (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
    (N count : Nat) (path : (code ctx noQuantum N count).Path) :
    (code ctx noQuantum N count).resourcePool path ≤ eventEnvelope N count := by
  refine (congrArg ResourcePool.ofList (code_eventTrace ctx noQuantum N count path)).le.trans ?_
  rw [ResourcePool.ofList_cons]
  exact add_le_add le_rfl
    (NativeBatch.code_pool_le (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count path.2)

/-- The actual preparation has unit duration and does not replace any later reset/reload work. -/
theorem code_unitDepth_le (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
    (N count : Nat) (path : (code ctx noQuantum N count).Path) :
    (code ctx noQuantum N count).depth (fun _ => 1) path ≤ depthBound N count :=
  Nat.add_le_add_left
    (NativeBatch.code_unitDepth_le (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count path.2) 1

end NativePreparedBatch

end

end QuantumAlg.Factoring.ShorStyle.Canonical
