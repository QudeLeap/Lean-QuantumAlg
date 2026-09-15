/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Budget
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Execution.Trace

/-!
# Events and depth of the actual decoded order sample

The same sampling path is followed by the real stored-bit decoder. Its
conditional increments contribute only when selected, while the independent
limit permits one shift and increment per original phase bit.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

/-- Every actual complete path fits the original sample plus fixed-width decoder allowance. -/
theorem code_events_le {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).resourcePool path ≤ eventBudget N x t n := by
  change ResourcePool.ofList
    ((Sampling.code A).eventTrace path.1 ++ (decoderCode t n).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (Sampling.code A).resourcePool path.1 + (decoderCode t n).resourcePool path.2 ≤ _
  rw [Sampling.code_events]
  exact add_le_add le_rfl
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
      path.2)

/-- Actual source and decoding dependencies satisfy the explicit complete duration limit. -/
theorem code_depth_le {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).depth (fun _ => 1) path ≤ depthBudget t := by
  change (Sampling.code A).depth (fun _ => 1) path.1 +
    (decoderCode t n).depth (fun _ => 1) path.2 ≤ _
  rw [Sampling.code_depth]
  have decoded :=
    ClassicalRoutines.TerminalDecode.terminalDecode_routine_depth_le
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
      (fun _ => 1) path.2
  change (decoderCode t n).depth (fun _ => 1) path.2 ≤ t * (1 + 1) at decoded
  unfold depthBudget
  omega

end

end QuantumAlg.OrderFinding.Exact
