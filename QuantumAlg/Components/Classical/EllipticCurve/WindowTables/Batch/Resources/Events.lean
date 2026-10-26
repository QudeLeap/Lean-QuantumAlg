/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting.Events

/-!
# Complete native event allowances for the original batch inversion

Each forward row writes its saved product and multiplies once. Each reverse
row multiplies twice and overwrites its denominator. The nonempty branch
also pays its initial word copy and the one shared raw coefficient computation.
The allowance retains every native width coordinate and the empty identity.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

/-- All complete native labels of a forward row. -/
def forwardEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model :=
  Accounting.rowWriteEnvelope model width length + multiplyEnvelope model width

/-- All complete native labels of a reverse row. -/
def reverseEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model :=
  multiplyEnvelope model width +
    (multiplyEnvelope model width + Accounting.rowWriteEnvelope model width length)

/-- Independent finite native pool for the original empty or nonempty batch. -/
def envelope (model : ExecutionModel) [BitWord.Selected model] {width : Nat}
    (length : Nat) (spec : ModulusSpec width) (count : Nat) : ResourcePool model :=
  if count = 0 then 0 else
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width width))) +
      (count • forwardEnvelope model width length +
        (Field.Native.coefficientEnvelope model spec + count • reverseEnvelope model width length))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat} (frame : BatchFrame ctx width length)

/-- The same actual forward path emits exactly the independent write and product pool. -/
lemma forwardStep_pool (index : Fin length)
    (path : (frame.forwardStep (model := model) index).Path) :
    (frame.forwardStep (model := model) index).resourcePool path =
      forwardEnvelope model width length := by
  dsimp only [forwardStep, Circuit.Path] at path ⊢
  rw [Accounting.seq_pool, Accounting.rowWrite_pool, nativePower_scopedMultiply_pool]
  rfl

/-- Both true reverse products and the original row overwrite remain charged. -/
lemma reverseStep_pool (index : Fin length)
    (path : (frame.reverseStep (model := model) index).Path) :
    (frame.reverseStep (model := model) index).resourcePool path =
      reverseEnvelope model width length := by
  dsimp only [reverseStep, Circuit.Path] at path ⊢
  rw [Accounting.seq_pool, Accounting.seq_pool,
    nativePower_scopedMultiply_pool, nativePower_scopedMultiply_pool, Accounting.rowWrite_pool]
  rfl

/-- Increasing traversal sums the actual forward rows without expanding their finite count. -/
lemma forwardPass_pool_le (count : Nat) (fits : count < length)
    (path : (frame.forwardPass (model := model) count fits).Path) :
    (frame.forwardPass (model := model) count fits).resourcePool path ≤
      count • forwardEnvelope model width length := by
  apply Accounting.range_pool_le
  intro index selected
  exact (frame.forwardStep_pool _ selected).le

/-- Decreasing traversal retains the same independent reverse-row allowance. -/
lemma reversePass_pool_le (count : Nat) (fits : count < length)
    (path : (frame.reversePass (model := model) count fits).Path) :
    (frame.reversePass (model := model) count fits).resourcePool path ≤
      count • reverseEnvelope model width length := by
  apply Accounting.range_pool_le
  intro index selected
  exact (frame.reverseStep_pool _ selected).le

/-- Every actual batch path obeys the complete independent native-event allowance. -/
lemma circuit_pool_le (spec : ModulusSpec width) (count : Nat) (fits : count < length) :
    ∀ path : (frame.circuit (model := model) spec count fits).Path,
      (frame.circuit (model := model) spec count fits).resourcePool path ≤
        envelope model length spec count := by
  unfold circuit envelope
  by_cases empty : count = 0
  · rw [if_pos empty, if_pos empty]
    intro path
    exact le_rfl
  · rw [if_neg empty, if_neg empty]
    intro path
    have initialized :
        (BitWord.instruction (execution := model)
          (.wordResize width width ctx frame.one frame.work.product)).resourcePool path.1 =
        ResourcePool.singleton (.classicalOperation
          (BitWord.selectedCoordinate (execution := model) (.wordResize width width))) := by
      rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
      rfl
    apply Accounting.seq_pool_le _ _ _ _ path initialized.le
    apply Accounting.seq_pool_le _ _ _ _ path.2
      (frame.forwardPass_pool_le count fits path.2.1)
    exact Accounting.seq_pool_le _ _ _ _ path.2.2
      (Field.Native.coefficientIntoWord_pool_le spec _ _ path.2.2.1)
      (frame.reversePass_pool_le count fits path.2.2.2)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
