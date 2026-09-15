/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Resources

/-!
# Actual native resources under complete bank placement

The exact ordered-wire correspondence only reindexes the real unitary and
constant-X program. It introduces no gate or depth change. The source seed
reload is bounded independently by one X per physical bank position; its
actual trace retains the exact constant-dependent number of X occurrences.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement

noncomputable section

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Actual placement preserves the complete native event budget of the selected source member. -/
theorem member_pool_le (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (memberProgram N sameWires parameter).eventCost ≤ NativeQuantum.eventBudget N := by
  rw [memberProgram, UnitaryCircuit.reindex_eventCost]
  exact NativeQuantum.program_pool_le parameter

/-- Actual bank placement preserves every serial or parallel dependency of the native member. -/
theorem member_unitDepth_le (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (memberProgram N sameWires parameter).evaluatedEventDepth (fun _ => 1) ≤
      NativeQuantum.depthBound N :=
  NativeQuantum.program_unitDepth_le parameter

private theorem reload_count_le (N : Nat) :
    EncodedBit.Word.BasisLoad.xCount (NativeQuantum.seedLabel N) ≤ 4 * modulusBits N :=
  (EncodedBit.Word.BasisLoad.basisLoad_count_le (NativeQuantum.seedLabel N)).trans_eq
    (NativeQuantum.totalQubits_eq_four_mul N)

/-- A fixed width-only native allowance bounds every actual X emitted by seed reload. -/
theorem reload_pool_le : (reloadProgram N sameWires).eventCost ≤
    ResourcePool.singleton (.gate (.builtin "x")) (4 * modulusBits N) := by
  rw [reloadProgram, UnitaryCircuit.reindex_eventCost,
    EncodedBit.Word.BasisLoad.basisLoad_eventCost, ResourcePool.le_iff_count]
  intro event
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  by_cases same : Resource.Event.gate (.builtin "x") = event
  · simpa only [if_pos same, Nat.mul_one] using reload_count_le N
  · simp only [if_neg same, Nat.mul_zero, Nat.le_refl]

/-- The actual sequential X load uses no more serial steps than the physical bank width. -/
theorem reload_unitDepth_le :
    (reloadProgram N sameWires).evaluatedEventDepth (fun _ => 1) ≤ 4 * modulusBits N :=
  (EncodedBit.Word.BasisLoad.basisLoad_unitDepth (NativeQuantum.seedLabel N)).le.trans
    (reload_count_le N)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement
