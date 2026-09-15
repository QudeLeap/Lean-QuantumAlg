/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Resources

/-!
# Complete independent native events and depth of the actual Shor circuit

One actual bank preparation prefixes every full sampled quantum round. The
same stored tuples then feed the complete native first-success recovery scan,
including all order, power, GCD, guard and packaging operations. Actual result
retention adds its storage, accounted for in NativeSpace, and introduces no
fictitious arithmetic event. Both budgets are specified independently by the
public modulus and actual finite round count.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

noncomputable section

/-- Independent native ledger for one preparation, all sampling rounds and complete recovery. -/
def eventBudget (N count : Nat) : ResourcePool .quantum :=
  NativePreparedBatch.eventEnvelope N count + NativeFactorScan.eventEnvelope .quantum N count

/-- All actual sampled quantum and native recovery dependencies contribute to the serial bound. -/
def depthBudget (N count : Nat) : Nat :=
  NativePreparedBatch.depthBound N count + NativeFactorScan.depthBound N count

private theorem recoveryCode_pool_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryCode source count).Path) :
    (recoveryCode source count).resourcePool path ≤
      NativeFactorScan.eventEnvelope .quantum N count := by
  have placed : (recoveryCode source count).resourcePool path =
      (NativeFactorScan.Scope.code source (visitInputs N count)
        (resultRef N count)).resourcePool path := rfl
  refine placed.le.trans ?_
  simpa only [visitInputs, List.length_ofFn] using
    NativeFactorScan.Scope.code_pool_le source (visitInputs N count) (resultRef N count) path

private theorem recovery_pool_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryStage source count).Path) :
    (recoveryStage source count).resourcePool path ≤
      NativeFactorScan.eventEnvelope .quantum N count :=
  recoveryCode_pool_le source count path.2

/-- Every native event emitted by the one complete actual run fits the independent full ledger. -/
theorem code_pool_le {N : Nat} (source : Input N) (count : Nat)
    (path : (code source count).Path) :
    (code source count).resourcePool path ≤ eventBudget N count := by
  change ResourcePool.ofList
    ((NativePreparedBatch.code pre pre_quantumWires N count).eventTrace path.1 ++
      (recoveryStage source count).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (NativePreparedBatch.code_pool_le pre pre_quantumWires N count path.1)
    (recovery_pool_le source count path.2)

private theorem recoveryCode_unitDepth_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryCode source count).Path) :
    (recoveryCode source count).depth (fun _ => 1) path ≤ NativeFactorScan.depthBound N count := by
  have placed : (recoveryCode source count).depth (fun _ => 1) path =
      (NativeFactorScan.Scope.code source (visitInputs N count)
        (resultRef N count)).depth (fun _ => 1) path := rfl
  refine placed.le.trans ?_
  simpa only [visitInputs, List.length_ofFn] using
    NativeFactorScan.Scope.code_unitDepth_le source (visitInputs N count) (resultRef N count) path

private theorem recovery_unitDepth_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryStage source count).Path) :
    (recoveryStage source count).depth (fun _ => 1) path ≤ NativeFactorScan.depthBound N count :=
  (Nat.zero_add _).le.trans (recoveryCode_unitDepth_le source count path.2)

/-- The same complete run includes every serial native dependency of sampling and recovery. -/
theorem code_unitDepth_le {N : Nat} (source : Input N) (count : Nat)
    (path : (code source count).Path) :
    (code source count).depth (fun _ => 1) path ≤ depthBudget N count :=
  Nat.add_le_add (NativePreparedBatch.code_unitDepth_le pre pre_quantumWires N count path.1)
    (recovery_unitDepth_le source count path.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
