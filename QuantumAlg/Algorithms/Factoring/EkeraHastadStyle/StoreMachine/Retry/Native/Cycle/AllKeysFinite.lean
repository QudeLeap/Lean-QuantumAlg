/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.AllKeys

/-!
# All-input complete cycles of the actual native finite retry

The same first-plus-reused batch schedule serves every original `Input N`.
Each quantum cycle is one independently requested sampled and recovered batch;
the chronological selector is a separate classical tail. Actual predecessor
outputs establish the next seed domain and physical restart. The exact finite
source success law and full joint-state/resource contract come from the same
actual selected run, including zero trials and exceptional keys.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.AllKeysFinite

noncomputable section

open Execution ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The original source input requests each completed batch separately. -/
def plan (input : Input N) : (count : Nat) →
    CyclePlan RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => .classical (NativeFiniteRetry.AllKeys.problem base noQuantum input 0)
  | later + 1 => .seq (Finite.chainPlan base noQuantum input later)
      (.classical (Selection.problem (NativeRetryChain.resultRefs base noQuantum N later)))

/-- Exact all-input finite correctness with independently specified complete-batch boundaries. -/
def problem (input : Input N) (count : Nat) :
    CycleProblem RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  outcome := NativeFiniteRetry.AllKeys.problem base noQuantum input count
  plan := plan base noQuantum input count

/-- The unchanged selected execution follows the same first/reused batch code. -/
def schedule (input : Input N) : (count : Nat) →
    Circuit.CycleSchedule (plan base noQuantum input count)
      (NativeFiniteRetry.algorithm base noQuantum input count).run.code
  | 0 => .classical _
      { output := (NativeFiniteRetry.algorithm base noQuantum input 0).run.output
        certified := NativeFiniteRetry.AllKeys.solves base noQuantum input 0 }
      (Finite.emptyClassical base)
  | later + 1 => .seq _ _ (Finite.chainSchedule base noQuantum input later)
      (Selection.schedule (NativeRetryChain.resultRefs base noQuantum N later))
      (fun _ _ _ => ⟨True.intro, True.intro⟩)
      (.inl (Selection.onlyClassical
        (NativeRetryChain.resultRefs base noQuantum N later)))

/-- Full source success, joint state, resources and actual batch-by-batch cycle execution. -/
def certificate (input : Input N) (count : Nat) :
    Algorithm.CycleSolves (NativeFiniteRetry.algorithm base noQuantum input count)
      (problem base noQuantum input count) where
  correctness := NativeFiniteRetry.AllKeys.solves base noQuantum input count
  schedule := schedule base noQuantum input count
  entry := by
    intro Reference original _admitted
    cases count <;> exact ⟨True.intro, True.intro⟩

/-- Zero batches have no quantum cycle; positive counts share one independent batch allowance. -/
theorem maximumCycleDepth_le (input : Input N) (count : Nat)
    (path : (NativeFiniteRetry.algorithm base noQuantum input count).run.code.Path) :
    (certificate base noQuantum input count).maximumCycleDepth (fun _ => 1) path ≤
      Finite.maximumCycleDepthBound N count := by
  cases count with
  | zero => exact le_refl 0
  | succ later =>
      change max ((Finite.chainSchedule base noQuantum input later).maximumCycleDepth
        (fun _ => 1) path.1) 0 ≤ Finite.batchDepthBound N
      rw [max_zero]
      exact Finite.chainMaximum_le base noQuantum input later path.1

/-- Every original modulus and actual path obeys the parameterized complete-cycle ceiling. -/
theorem maximumCycleDepth_le_scalar (input : Input N) (count : Nat)
    (path : (NativeFiniteRetry.algorithm base noQuantum input count).run.code.Path) :
    (certificate base noQuantum input count).maximumCycleDepth (fun _ => 1) path ≤
      Finite.maximumCycleScalarBound N count :=
  (maximumCycleDepth_le base noQuantum input count path).trans
    (Finite.maximumCycleDepthBound_le_scalar N count)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.AllKeysFinite
