/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Support
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The minimal work suffix for a repeated elementary zero reflection

Small source widths and empty schedules need no work system. A nonempty
large-width schedule has exactly one arbitrary work system. The actual
physical placement preserves every source/work value and implements the
positive source reflection tensor identity, with its literal native ledger.
-/

namespace QuantumAlg.ZeroReflection.Workspace

noncomputable section

/-- One work wire is needed exactly for a nonempty large-width reflection schedule. -/
@[expose] public def helperWidth (n k : Nat) : Nat :=
  if k = 0 ∨ n ≤ 3 then 0 else 1

/-- The actual source register and its selected work suffix. -/
@[implicit_reducible, expose] public def totalQubits (n k : Nat) : Nat := n + helperWidth n k

theorem helperWidth_zero_iterations (n : Nat) : helperWidth n 0 = 0 := by
  simp [helperWidth]

theorem helperWidth_small (n k : Nat) (small : n ≤ 3) : helperWidth n k = 0 := by
  simp [helperWidth, small]

theorem helperWidth_large (n k : Nat) (nonzero : k ≠ 0) (large : ¬n ≤ 3) :
    helperWidth n k = 1 := by
  simp [helperWidth, nonzero, large]

/-- The exact elementary source reflection is selected only for an executed iteration. -/
def reflection : (n k : Nat) → k ≠ 0 → UnitaryCircuit (Qubits (totalQubits n k))
  | 0, k, _ => (ZeroReflection.Small.program 0 (by omega)).idleSuffix
      (ZeroReflection.Small.program_physical_idx_subset_range 0 (by omega)) (helperWidth 0 k)
  | n + 1, k, nonzero =>
      if small : n + 1 ≤ 3 then
        (ZeroReflection.Small.program (n + 1) small).idleSuffix
          (ZeroReflection.Small.program_physical_idx_subset_range (n + 1) small)
          (helperWidth (n + 1) k)
      else
        UnitaryCircuit.reindex
          (finCongr (congrArg (fun width : Nat => 2 ^ width)
            (show n + 1 + 1 = totalQubits (n + 1) k by
              rw [totalQubits, helperWidth_large (n + 1) k nonzero small])))
          (ZeroReflection.OneDirty.program n)

theorem reflection_contained (n k : Nat) (nonzero : k ≠ 0) :
    (reflection n k nonzero).physical_idx ⊆ List.range (totalQubits n k) := by
  cases n with
  | zero =>
      exact UnitaryCircuit.idleSuffix_physical_idx_subset_range
        (ZeroReflection.Small.program 0 (by omega))
        (ZeroReflection.Small.program_physical_idx_subset_range 0 (by omega)) (helperWidth 0 k)
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small]
        exact UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _
      · rw [reflection, dif_neg small]
        change (ZeroReflection.OneDirty.program n).physical_idx ⊆ List.range (totalQubits (n + 1) k)
        rw [totalQubits, helperWidth_large (n + 1) k nonzero small]
        exact ZeroReflection.OneDirty.program_physical_idx_subset_range n

theorem reflection_matrix (n k : Nat) (nonzero : k ≠ 0) :
    (reflection n k nonzero).matrix =
      UnitaryOperator.tensor (ZeroReflection.zeroReflectionOperator n)
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.idleSuffix_matrix, ZeroReflection.Small.program_matrix]
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.idleSuffix_matrix,
          ZeroReflection.Small.program_matrix]
      · rw [reflection, dif_neg small, UnitaryCircuit.reindex_matrix,
          ZeroReflection.OneDirty.program_matrix]
        have transport (suffix : Nat) (same : 1 = suffix) :
            UnitaryOperator.reindex
              (finCongr (congrArg (fun width : Nat => 2 ^ width)
                (congrArg (fun extra => n + 1 + extra) same)))
              (UnitaryOperator.tensor (ZeroReflection.zeroReflectionOperator (n + 1))
                (1 : UnitaryOperator (Qubits 1))) =
              UnitaryOperator.tensor (ZeroReflection.zeroReflectionOperator (n + 1))
                (1 : UnitaryOperator (Qubits suffix)) := by
          cases same
          rfl
        exact transport (helperWidth (n + 1) k)
          (helperWidth_large (n + 1) k nonzero small).symm

theorem reflection_eventCost (n k : Nat) (nonzero : k ≠ 0) :
    (reflection n k nonzero).eventCost = ZeroReflection.elementaryEventPool n := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.idleSuffix_eventCost, ZeroReflection.Small.program_eventCost]
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.idleSuffix_eventCost,
          ZeroReflection.Small.program_eventCost]
      · rw [reflection, dif_neg small, UnitaryCircuit.reindex_eventCost]
        exact ZeroReflection.OneDirty.program_eventCost n (by omega)

theorem reflection_unitDepth (n k : Nat) (nonzero : k ≠ 0) :
    (reflection n k nonzero).evaluatedEventDepth (fun _ => 1) =
      ZeroReflection.elementaryGateCount n := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.idleSuffix_evaluatedEventDepth,
        ZeroReflection.Small.program_unitDepth]
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.idleSuffix_evaluatedEventDepth,
          ZeroReflection.Small.program_unitDepth]
      · rw [reflection, dif_neg small]
        change (ZeroReflection.OneDirty.program n).evaluatedEventDepth (fun _ => 1) = _
        exact ZeroReflection.OneDirty.program_unitDepth n (by omega)

end

end QuantumAlg.ZeroReflection.Workspace
