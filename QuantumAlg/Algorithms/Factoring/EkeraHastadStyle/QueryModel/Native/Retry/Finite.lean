/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty

/-!
# Every finite total count on the actual original oracle bank

Zero batches use the existing real allocation of an empty optional result.
Every positive count uses the original-width retry with its one physical
bank, paid reset between samples and final paid pack into the factor cell.
The natural count chooses only between these existing actual programs.
Every branch lists all surviving caller resources and allocated storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Zero retains its real result; every positive count retains the same sole oracle bank. -/
def context : Nat → RuntimeCtx .quantum
  | 0 => NativeRetryEmpty.context base N
  | _ + 1 => Retry.context base noQuantum N

/-- Total count selects the existing empty allocation or the actual positive retry program. -/
def code (input : Input N) : (totalRounds : Nat) →
    Circuit base (context base noQuantum N totalRounds)
  | 0 => NativeRetryEmpty.code base N
  | laterCount + 1 => Retry.code base noQuantum N input laterCount

/-- The actual finite result has the same optional factor shape and complete output manifest. -/
def run (input : Input N) : (totalRounds : Nat) →
    AlgorithmRun base (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => NativeRetryEmpty.run base N
  | laterCount + 1 => Retry.run base noQuantum N input laterCount

/-- Every finite branch executes exactly its structurally selected actual program. -/
theorem nativeOracle_finiteRetry_run_code (input : Input N) (totalRounds : Nat) :
    (run base noQuantum N input totalRounds).code = code base noQuantum N input totalRounds := by
  cases totalRounds <;> rfl

/-- No caller resource, live sample cell or physical wire is omitted from the finite output. -/
theorem nativeOracle_finiteRetry_output_listing (input : Input N) (totalRounds : Nat) :
    (run base noQuantum N input totalRounds).output.listing =
      (context base noQuantum N totalRounds).keys := by
  cases totalRounds <;> rfl

/-- The zero-count branch allocates no quantum bank. -/
theorem nativeOracle_finiteRetry_zero_wires :
    (context base noQuantum N 0).quantumWires = base.quantumWires := rfl

/-- Every positive count has exactly the original oracle's one physical bank. -/
theorem nativeOracle_finiteRetry_positive_wires (laterCount : Nat) :
    (context base noQuantum N (laterCount + 1)).quantumWires = (layout N).wires :=
  nativeOracle_retry_wires base noQuantum N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
