/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Fixed live-space bound across completed EH batches

Every later batch uses the same retained cells and quantum bank. Its pack
uses those existing cells; its physical reset uses scratch already covered by
the original recovery allowance. The maximum resident and auxiliary space
therefore does not grow with the number of completed batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private lemma completed_context_resident :
    (Retry.context base noQuantum N).residentSpace ≤
      Retry.additionalSpace N + base.residentSpace := by
  rw [Retry.declaredRetry_context_residentSpace]
  intro axis
  change (Batch.retainedSpace N axis + Retry.selectorSpace N axis) +
    base.residentSpace axis ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.residentSpace axis
  omega

private lemma completed_context_auxiliary :
    (Retry.context base noQuantum N).auxiliarySpace ≤
      Retry.additionalSpace N + base.auxiliarySpace := by
  rw [Retry.declaredRetry_context_auxiliarySpace]
  intro axis
  change (Batch.retainedSpace N axis + Retry.selectorSpace N axis) +
    base.auxiliarySpace axis ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.auxiliarySpace axis
  omega

/-- A later batch's recovery, existing-cell pack and actual reset all fit the
same fixed resident allowance. -/
lemma nextCompleted_peakResidentSpace_le
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).peakResidentSpace path ≤
      Retry.additionalSpace N + base.residentSpace := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N)).seq
      (reset base noQuantum N)).peakResidentSpace path ≤ _
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact Retry.next_resident base noQuantum N input path.1.1
    · have packPeak :
          (Retry.pack base noQuantum N).peakResidentSpace path.1.2 =
            (Retry.context base noQuantum N).residentSpace := by
        funext axis
        exact Nat.max_zero _
      exact packPeak.trans_le (completed_context_resident base noQuantum N)
  · exact reset_resident base noQuantum N path.2

/-- The same complete later batch fits the original auxiliary allowance. -/
lemma nextCompleted_peakAuxiliarySpace_le
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).peakAuxiliarySpace path ≤
      Retry.additionalSpace N + base.auxiliarySpace := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N)).seq
      (reset base noQuantum N)).peakAuxiliarySpace path ≤ _
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact Retry.next_auxiliary base noQuantum N input path.1.1
    · have packPeak :
          (Retry.pack base noQuantum N).peakAuxiliarySpace path.1.2 =
            (Retry.context base noQuantum N).auxiliarySpace := by
        funext axis
        exact Nat.max_zero _
      exact packPeak.trans_le (completed_context_auxiliary base noQuantum N)
  · exact reset_auxiliary base noQuantum N path.2

/-- Arbitrarily many actual completed later batches reuse one fixed resident
bank and store allowance. -/
lemma laterCompleted_peakResidentSpace_le (laterCount : Nat)
    (path : (laterCompletedCode base noQuantum N input laterCount).Path) :
    (laterCompletedCode base noQuantum N input laterCount).peakResidentSpace path ≤
      Retry.additionalSpace N + base.residentSpace := by
  exact Circuit.forRange_resident_le laterCount
    (fun _ => nextCompletedCode base noQuantum N input)
    (Retry.additionalSpace N + base.residentSpace)
    (completed_context_resident base noQuantum N)
    (fun _ => nextCompleted_peakResidentSpace_le base noQuantum N input) path

/-- Repeating the complete later batch also keeps one fixed auxiliary bound. -/
lemma laterCompleted_peakAuxiliarySpace_le (laterCount : Nat)
    (path : (laterCompletedCode base noQuantum N input laterCount).Path) :
    (laterCompletedCode base noQuantum N input laterCount).peakAuxiliarySpace path ≤
      Retry.additionalSpace N + base.auxiliarySpace := by
  exact Circuit.forRange_auxiliary_le laterCount
    (fun _ => nextCompletedCode base noQuantum N input)
    (Retry.additionalSpace N + base.auxiliarySpace)
    (completed_context_auxiliary base noQuantum N)
    (fun _ => nextCompleted_peakAuxiliarySpace_le base noQuantum N input) path

/-- The first completed batch and all later completed batches meet the same
positive-count resident-space contract as the preserved finite run. -/
lemma completed_peakResidentSpace_le (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).peakResidentSpace path ≤
      Finite.additionalSpace N (laterCount + 1) + base.residentSpace := by
  change (completedCode base noQuantum N input laterCount).peakResidentSpace path ≤
    Retry.additionalSpace N + base.residentSpace
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact firstCompleted_peakResidentSpace_le base noQuantum input path.1
  · exact laterCompleted_peakResidentSpace_le base noQuantum N input laterCount path.2

/-- The same actual completed run meets the preserved positive-count
auxiliary-space contract. -/
lemma completed_peakAuxiliarySpace_le (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).peakAuxiliarySpace path ≤
      Finite.additionalSpace N (laterCount + 1) + base.auxiliarySpace := by
  change (completedCode base noQuantum N input laterCount).peakAuxiliarySpace path ≤
    Retry.additionalSpace N + base.auxiliarySpace
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact firstCompleted_peakAuxiliarySpace_le base noQuantum input path.1
  · exact laterCompleted_peakAuxiliarySpace_le base noQuantum N input laterCount path.2

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
