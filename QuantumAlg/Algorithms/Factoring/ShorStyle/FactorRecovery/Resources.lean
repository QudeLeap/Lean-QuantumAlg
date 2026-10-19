/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Resources

/-!
# Actual native event bounds for complete stored-sample factor recovery

Every stored flag selects its real continuation. The guard, nominal base and
order conversions, complete order recovery, half-power, GCD selection, even
exception and final output pack are all counted from the same circuit path.
Alternative branches use the independent coordinatewise maxima of their
actual native event budgets.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The actual two reduction stages fit their independently specified event coordinates. -/
lemma reduce_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce (model := model) source cells output).Path) :
    (reduce (model := model) source cells output).resourcePool path ≤ reduceEnvelope model N := by
  change ResourcePool.ofList
    ((NativeHalfPower.code (model := model) source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower).eventTrace path.1 ++
      (NativeHalfFactorScope.code (model := model) (halfRead cells) output).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (NativeHalfPower.code_pool_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1)
    (NativeHalfFactorScope.code_pool_le (halfRead cells) output path.2)

/-- All five runtime guard operations are genuine native event occurrences. -/
lemma guardOrder_pool (cells : Cells ctx N) (path : (guardOrder (model := model) cells).Path) :
    (guardOrder (model := model) cells).resourcePool path = ResourcePool.ofList (guardEvents model
        N) := by
  unfold Circuit.resourcePool
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (clearZeroOp cells)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model) (evenOrderOp cells)).eventTrace path.2.1 ++
        ((BitWord.instruction (execution := model) (positiveOrderOp cells)).eventTrace path.2.2.1 ++
          ((BitWord.instruction (execution := model) (positiveEvenOp cells)).eventTrace
              path.2.2.2.1 ++
            (BitWord.instruction (execution := model) (acceptedOrderOp cells)).eventTrace
                path.2.2.2.2)))) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma checkedBranch_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).resourcePool
            path ≤
      ResourcePool.max (packBudget model N) (reduceEnvelope model N) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (BitWord.instruction (execution := model) (packOutputOp cells output)).Path at path
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (packOutputOp cells output)).eventTrace path)
              ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        exact ResourcePool.le_max_left _ _
      · exact (reduce_pool_le source cells output path).trans (ResourcePool.le_max_right _ _)

/-- Actual order rejection still consumes its output pack after the complete runtime guard. -/
lemma checkedOrder_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder (model := model) source cells output).Path) :
    (checkedOrder (model := model) source cells output).resourcePool path ≤ checkedEnvelope model
        N := by
  change ResourcePool.ofList ((guardOrder (model := model) cells).eventTrace path.1 ++
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).eventTrace
            path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (guardOrder_pool cells path.1).le
    (checkedBranch_pool_le source cells output path.2)

/-- The real early-factor branch and the full order route fit the independent dispatch maximum. -/
lemma dispatch_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch (model := model) source parameter cells output).Path) :
    (dispatch (model := model) source parameter cells output).resourcePool path ≤ dispatchEnvelope
        model N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (checkedOrder_pool_le source cells output path).trans
          (ResourcePool.le_max_right _ _)
      · change (BitWord.instruction (execution := model)
          (packEarlyOp parameter output)).Path at path
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (packEarlyOp parameter output)).eventTrace
              path) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        exact ResourcePool.le_max_left _ _

/-- The stored base and measured word enter the complete real native order-recovery program. -/
lemma recovered_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered (model := model) source parameter phase cells output).Path) :
    (recovered (model := model) source parameter phase cells output).resourcePool path ≤
      recoveredEnvelope model N := by
  change ResourcePool.ofList ((BitWord.instruction (execution := model) (packBaseOp parameter
      cells)).eventTrace path.1 ++
    ((OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
        cells.base.toCStorageRef)
      phase cells.order).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (unpackOrderOp cells)).eventTrace path.2.2.1 ++
        (dispatch (model := model) source parameter cells output).eventTrace path.2.2.2))) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl
    (add_le_add (OrderRecovery.Native.nativeRecovery_into_pool_le
      (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1)
      (add_le_add le_rfl (dispatch_pool_le source parameter cells output path.2.2.2)))

/-- The known even exception counts actual flag writes, the literal load and the option pack. -/
lemma evenModulus_pool_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus (model := model) cells output).Path) :
    (evenModulus (model := model) cells output).resourcePool path ≤ evenEnvelope model N := by
  change ResourcePool.ofList ((BitWord.instruction (execution := model) (clearActiveOp
      cells)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (setActiveOp cells)).eventTrace path.2.1 ++
      ((ConstantWord.circuit (model := model) cells.halfPower 2).eventTrace path.2.2.1 ++
        (BitWord.instruction (execution := model) (packOutputOp cells output)).eventTrace
            path.2.2.2))) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, ResourcePool.ofList_append,
    ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (ConstantWord.constantWord_pool_le cells.halfPower 2 path.2.2.1) le_rfl))

/-- Every complete actual factor-tail path fits the independently selected native event budget. -/
lemma code_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source parameter phase cells output).Path) :
    (code (model := model) source parameter phase cells output).resourcePool path ≤ eventEnvelope
        model N := by
  have allPaths : ∀ selected : (code (model := model) source parameter phase cells output).Path,
      (code (model := model) source parameter phase cells output).resourcePool selected ≤
          eventEnvelope model N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code (model := model) source parameter phase cells output = evenModulus (model
        := model) cells output :=
        if_pos exceptional
      rw [same]
      simpa only [eventEnvelope, if_pos exceptional] using evenModulus_pool_le cells output
    · have same : code (model := model) source parameter phase cells output =
          recovered (model := model) source parameter phase cells output := if_neg exceptional
      rw [same]
      simpa only [eventEnvelope, if_neg exceptional] using
        recovered_pool_le source parameter phase cells output
  exact allPaths path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
