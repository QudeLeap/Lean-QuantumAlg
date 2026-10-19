/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Coordinates
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Exact granted queries of independently completed EH batches

The actual first batch and each further completed segment contribute exactly
sixteen granted group queries on every path. The added selector packs and
physical bank resets are present in the execution but contribute no query.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private abbrev groupQuery : Resource.Event (model N) := .oracle .groupOperation

/-- Every further real completed batch contributes sixteen granted queries
on each actual chronological path. -/
lemma laterCompleted_query_count (count : Nat)
    (path : (laterCompletedCode base noQuantum N input count).Path) :
    ResourcePool.count (groupQuery N)
      ((laterCompletedCode base noQuantum N input count).resourcePool path) =
        16 * count := by
  have exactCount := Circuit.forRange_event_count (groupQuery N) count
    (fun _ => nextCompletedCode base noQuantum N input) 16
    (fun _ path => nextCompleted_query_count base noQuantum N input path) path
  simpa only [laterCompletedCode, Nat.mul_comm] using exactCount

/-- The physically completed positive execution pays exactly sixteen queries
per requested batch, including the one-batch and arbitrary-repeat cases. -/
lemma completed_query_count (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    ResourcePool.count (groupQuery N)
      ((completedCode base noQuantum N input laterCount).resourcePool path) =
        16 * (laterCount + 1) := by
  change ResourcePool.count (groupQuery N)
    ((firstCompletedAlgorithm base noQuantum input).run.code.resourcePool path.1 +
      (laterCompletedCode base noQuantum N input laterCount).resourcePool path.2) = _
  rw [ResourcePool.count_add]
  have first : ResourcePool.count (groupQuery N)
      ((firstCompletedAlgorithm base noQuantum input).run.code.resourcePool path.1) = 16 :=
    firstCompleted_query_count base noQuantum input path.1
  have later := laterCompleted_query_count base noQuantum N input laterCount path.2
  omega

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
