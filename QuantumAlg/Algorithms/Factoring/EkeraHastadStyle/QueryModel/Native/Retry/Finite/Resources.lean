/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Space

/-!
# Actual resources at every finite original-oracle retry count

Zero batches allocate only their real empty optional result and emit no
native event. Every positive count uses the complete original-bank retry,
including all requested reset/sampling/recovery/selection work and its final
paid pack. Its fixed storage allowance is independent of the positive count.
These casewise scalar budgets belong to the existing actual finite program.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution

noncomputable section

/-- Zero has no event; every positive count pays the full actual original-bank retry. -/
def eventBudget (N : Nat) : Nat → ResourcePool .quantum
  | 0 => 0
  | laterCount + 1 => Retry.eventBudget N laterCount

/-- Event durations remain arbitrary and the positive branch keeps its real critical paths. -/
def durationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat → Nat
  | 0 => 0
  | laterCount + 1 => Retry.durationBudget N laterCount duration

/-- Zero allocates its output; positive counts share the same physical retained storage. -/
def additionalSpace (N : Nat) : Nat → SpacePool .quantum
  | 0 => NativeRetryEmpty.additionalSpace N
  | _ + 1 => Retry.additionalSpace N

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Each finite actual path is bounded by the independent event allowance for its total count. -/
theorem nativeOracle_finiteRetry_resourcePool_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum N input totalRounds).Path) :
    (code base noQuantum N input totalRounds).resourcePool path ≤ eventBudget N totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_pool base N path).le
  | succ laterCount =>
      exact nativeOracle_retry_resourcePool_le base noQuantum N input laterCount path

/-- Every actual finite path preserves all dependency charges for arbitrary event durations. -/
theorem nativeOracle_finiteRetry_depth_le (input : Input N) (totalRounds : Nat)
    (duration : Resource.Event .quantum → Nat)
    (path : (code base noQuantum N input totalRounds).Path) :
    (code base noQuantum N input totalRounds).depth duration path ≤
      durationBudget N duration totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_depth base N duration path).le
  | succ laterCount =>
      exact nativeOracle_retry_depth_le base noQuantum N input laterCount duration path

/-- The actual finite resident peak includes every caller resource and every retained output. -/
theorem nativeOracle_finiteRetry_peakResidentSpace_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum N input totalRounds).Path) :
    (code base noQuantum N input totalRounds).peakResidentSpace path ≤
      additionalSpace N totalRounds + base.residentSpace := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_resident base N path).le.trans_eq (add_comm _ _)
  | succ laterCount =>
      exact nativeOracle_retry_peakResidentSpace_le base noQuantum N input laterCount path

/-- The actual finite auxiliary peak keeps original roles and all real allocated storage. -/
theorem nativeOracle_finiteRetry_peakAuxiliarySpace_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum N input totalRounds).Path) :
    (code base noQuantum N input totalRounds).peakAuxiliarySpace path ≤
      additionalSpace N totalRounds + base.auxiliarySpace := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_auxiliary base N path).le.trans_eq (add_comm _ _)
  | succ laterCount =>
      exact nativeOracle_retry_peakAuxiliarySpace_le base noQuantum N input laterCount path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
