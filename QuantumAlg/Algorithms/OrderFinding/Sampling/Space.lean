/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Space

/-!
# Empty-input sampling space

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

private theorem pre_residentSpace : pre.residentSpace = 0 := by
  ext axis
  cases axis <;> rfl

private theorem pre_auxiliarySpace : pre.auxiliarySpace = 0 := rfl

/-- The common output has the original empty-input capacity. -/
theorem post_residentSpace (t n : Nat) : (post t n).residentSpace = spaceBudget t n := by
  simpa only [Framed.residentBudget, pre_residentSpace, add_zero] using
    Framed.post_residentSpace pre pre_quantumWires t n

theorem post_auxiliarySpace (t n : Nat) : (post t n).auxiliarySpace = spaceBudget t n := by
  simpa only [Framed.auxiliaryBudget, pre_auxiliarySpace, add_zero] using
    Framed.post_auxiliarySpace pre pre_quantumWires t n

/-- The same actual path respects the independently stated resident budget. -/
theorem code_residentSpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).peakResidentSpace path ≤ spaceBudget t n := by
  simpa only [code, Framed.residentBudget, pre_residentSpace, add_zero] using
    Framed.code_residentSpace pre pre_quantumWires A path

/-- The same actual path respects the independently stated auxiliary budget. -/
theorem code_auxiliarySpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).peakAuxiliarySpace path ≤ spaceBudget t n := by
  simpa only [code, Framed.auxiliaryBudget, pre_auxiliarySpace, add_zero] using
    Framed.code_auxiliarySpace pre pre_quantumWires A path

end

end QuantumAlg.OrderFinding.Sampling
