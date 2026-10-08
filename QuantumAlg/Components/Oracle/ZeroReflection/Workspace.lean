/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Qubit
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

private abbrev physical (width : Nat) : QubitLayout width where
  physical_idx := Fin.val
  physical_idx_injective := Fin.val_injective

private def castCircuit (oracles : OracleModel) {left right : Nat} (same : left = right)
    (body : UnitaryCircuit AlgorithmGate.model oracles (physical left).toQuantum) :
    UnitaryCircuit AlgorithmGate.model oracles (physical right).toQuantum := same ▸ body

private theorem castCircuit_matrix (oracles : OracleModel) {left right : Nat}
    (same : left = right)
    (body : UnitaryCircuit AlgorithmGate.model oracles (physical left).toQuantum) :
    (castCircuit oracles same body).binaryMatrix =
      UnitaryOperator.reindex (finCongr (congrArg (fun width => 2 ^ width) same))
        body.binaryMatrix := by
  cases same
  apply Subtype.ext
  rfl

private theorem castCircuit_eventCost (oracles : OracleModel) {left right : Nat}
    (same : left = right)
    (body : UnitaryCircuit AlgorithmGate.model oracles (physical left).toQuantum) :
    (castCircuit oracles same body).eventCost = body.eventCost := by
  cases same
  rfl

private theorem castCircuit_unitDepth (oracles : OracleModel) {left right : Nat}
    (same : left = right)
    (body : UnitaryCircuit AlgorithmGate.model oracles (physical left).toQuantum) :
    (castCircuit oracles same body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) := by
  cases same
  rfl

/-- Execute a source reflection with precisely the selected existing work suffix. -/
def reflection (oracles : OracleModel) : (n k : Nat) → k ≠ 0 →
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout
  | 0, k, _ => (Small.program oracles 0 (physical 0) (by omega)).onBinaryPrefix
      (helperWidth 0 k)
  | n + 1, k, nonzero =>
      if small : n + 1 ≤ 3 then
        (Small.program oracles (n + 1) (physical (n + 1)) small).onBinaryPrefix
          (helperWidth (n + 1) k)
      else
        castCircuit oracles
          (show n + 1 + 1 = totalQubits (n + 1) k by
            rw [totalQubits, helperWidth_large (n + 1) k nonzero small])
          (OneDirty.program oracles n (physical (n + 1 + 1)))

/-- Full matrix equality preserves the entire arbitrary work suffix and its correlations. -/
theorem reflection_matrix (oracles : OracleModel) (n k : Nat) (nonzero : k ≠ 0) :
    (reflection oracles n k nonzero).binaryMatrix =
      UnitaryOperator.tensor (zeroReflectionOperator n)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
      exact congrArg (fun operator => operator.tensor
        (1 : UnitaryOperator (Qubits (helperWidth 0 k))))
        (Small.program_matrix oracles 0 (physical 0) (by omega))
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
        exact congrArg (fun operator => operator.tensor
          (1 : UnitaryOperator (Qubits (helperWidth (n + 1) k))))
          (Small.program_matrix oracles (n + 1) (physical (n + 1)) small)
      · rw [reflection, dif_neg small, castCircuit_matrix]
        have actual := OneDirty.program_matrix oracles n (physical (n + 1 + 1))
        change (OneDirty.program oracles n (physical (n + 1 + 1))).binaryMatrix = _ at actual
        rw [actual]
        have transport (suffix : Nat) (same : 1 = suffix) :
            UnitaryOperator.reindex
              (finCongr (congrArg (fun width : Nat => 2 ^ width)
                (congrArg (fun extra => n + 1 + extra) same)))
              (UnitaryOperator.tensor (zeroReflectionOperator (n + 1))
                (1 : UnitaryOperator (Qubits 1))) =
              UnitaryOperator.tensor (zeroReflectionOperator (n + 1))
                (1 : UnitaryOperator (Qubits suffix)) := by
          cases same
          apply Subtype.ext
          rfl
        exact transport (helperWidth (n + 1) k)
          (helperWidth_large (n + 1) k nonzero small).symm

/-- Actual native multiplicities agree with the independently stated source-width budget. -/
theorem reflection_eventCost (oracles : OracleModel) (n k : Nat) (nonzero : k ≠ 0) :
    (reflection oracles n k nonzero).eventCost = elementaryEventPool oracles n := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
      exact Small.program_eventCost oracles 0 (physical 0) (by omega)
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
        exact Small.program_eventCost oracles (n + 1) (physical (n + 1)) small
      · rw [reflection, dif_neg small, castCircuit_eventCost]
        exact OneDirty.program_eventCost oracles n (physical (n + 1 + 1)) (by omega)

/-- The complete native sequence retains its independently bounded dependency depth. -/
theorem reflection_unitDepth (oracles : OracleModel) (n k : Nat) (nonzero : k ≠ 0) :
    (reflection oracles n k nonzero).evaluatedEventDepth (fun _ => 1) =
      elementaryGateCount n := by
  cases n with
  | zero =>
      rw [reflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
      exact Small.program_unitDepth oracles 0 (physical 0) (by omega)
  | succ n =>
      by_cases small : n + 1 ≤ 3
      · rw [reflection, dif_pos small, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
        exact Small.program_unitDepth oracles (n + 1) (physical (n + 1)) small
      · rw [reflection, dif_neg small, castCircuit_unitDepth]
        exact OneDirty.program_unitDepth oracles n (physical (n + 1 + 1)) (by omega)

end

end QuantumAlg.ZeroReflection.Workspace
