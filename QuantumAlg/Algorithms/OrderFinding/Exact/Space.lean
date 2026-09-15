/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Budget
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Space
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete live storage of the exact decoded sample

The decoder adds a real unsigned word and keeps every sampled system and
classical source representation. No terminal measurement releases quantum
storage, and actual path peaks satisfy the independent native capacities.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

/-- The complete final resident context has exactly the stated capacity. -/
theorem post_residentSpace (t n : Nat) : (post t n).residentSpace = spaceBudget t n := by
  rw [post, RuntimeCtx.residentSpace_addRetained, Sampling.post_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t + 2 * t = 3 * t
      omega
  | quantumSystems dimension =>
      change 0 + (if (2 : ℕ+) = dimension then t + n else 0) = _
      exact Nat.zero_add _

/-- All added systems and cells count as owned or retained auxiliary resources. -/
theorem post_auxiliarySpace (t n : Nat) : (post t n).auxiliarySpace = spaceBudget t n := by
  rw [post, RuntimeCtx.auxiliarySpace_addRetained, Sampling.post_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t + 2 * t = 3 * t
      omega
  | quantumSystems dimension =>
      change 0 + (if (2 : ℕ+) = dimension then t + n else 0) = _
      exact Nat.zero_add _

private theorem sampling_capacity_le (t n : Nat) :
    Sampling.spaceBudget t n ≤ spaceBudget t n := by
  intro axis
  cases axis with
  | classicalBits =>
      change 2 * t ≤ 3 * t
      omega
  | quantumSystems dimension => exact le_rfl

/-- Every actual resident peak includes both sampling and the retained decoder result. -/
theorem code_residentSpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).peakResidentSpace path ≤ spaceBudget t n := by
  refine (Circuit.peakResidentSpace_seq (Sampling.code A) (decoderCode t n) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Sampling.code_residentSpace A path.1).trans (sampling_capacity_le t n)
  · exact
      (ClassicalRoutines.TerminalDecode.terminalDecode_routine_resident_le
        (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
        path.2).trans_eq (post_residentSpace t n)

/-- The same path bounds every actual owned or retained auxiliary entry. -/
theorem code_auxiliarySpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).peakAuxiliarySpace path ≤ spaceBudget t n := by
  refine (Circuit.peakAuxiliarySpace_seq (Sampling.code A) (decoderCode t n) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Sampling.code_auxiliarySpace A path.1).trans (sampling_capacity_le t n)
  · exact
      (ClassicalRoutines.TerminalDecode.terminalDecode_routine_auxiliary_le
        (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
        path.2).trans_eq (post_auxiliarySpace t n)

end

end QuantumAlg.OrderFinding.Exact
