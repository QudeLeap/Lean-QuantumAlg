/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Accounting

/-!
# Exact query accounting at the all-count EH candidate endpoint

The original zero branch and every positive completed schedule retain the
same sixteen-granted-query-per-batch law on every actual execution path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

private abbrev groupQuery (N : Nat) : Resource.Event (model N) :=
  .oracle .groupOperation

/-- Zero and positive completed runs pay exactly the original granted query
formula on every path, with no exceptional-input restriction. -/
lemma completedAlgorithm_query_count (input : Input N) (count : Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.count (groupQuery N)
      ((completedAlgorithm base noQuantum input count).run.code.resourcePool path) =
        16 * count := by
  cases count with
  | zero =>
      change ResourcePool.count (groupQuery N) (0 : ResourcePool (model N)) = 0
      exact ResourcePool.count_zero _
  | succ laterCount =>
      exact Cleanup.completed_query_count base noQuantum N input laterCount path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
