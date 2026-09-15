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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual two reduction stages fit their independently specified event coordinates. -/
theorem reduce_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce source cells output).Path) :
    (reduce source cells output).resourcePool path ≤ reduceEnvelope kind N := by
  change ResourcePool.ofList
    ((NativeHalfPower.code source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower).eventTrace path.1 ++
      (NativeHalfFactorScope.code (halfRead cells) output).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (NativeHalfPower.code_pool_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1)
    (NativeHalfFactorScope.code_pool_le (halfRead cells) output path.2)

/-- All five runtime guard operations are genuine native event occurrences. -/
theorem guardOrder_pool (cells : Cells ctx N) (path : (guardOrder cells).Path) :
    (guardOrder cells).resourcePool path = ResourcePool.ofList (guardEvents kind N) := rfl

private theorem checkedBranch_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).resourcePool path ≤
      ResourcePool.max (packBudget kind N) (reduceEnvelope kind N) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact ResourcePool.le_max_left _ _
      · exact (reduce_pool_le source cells output path).trans (ResourcePool.le_max_right _ _)

/-- Actual order rejection still consumes its output pack after the complete runtime guard. -/
theorem checkedOrder_pool_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder source cells output).Path) :
    (checkedOrder source cells output).resourcePool path ≤ checkedEnvelope kind N := by
  change ResourcePool.ofList ((guardOrder cells).eventTrace path.1 ++
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (guardOrder_pool cells path.1).le
    (checkedBranch_pool_le source cells output path.2)

/-- The real early-factor branch and the full order route fit the independent dispatch maximum. -/
theorem dispatch_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch source parameter cells output).Path) :
    (dispatch source parameter cells output).resourcePool path ≤ dispatchEnvelope kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (checkedOrder_pool_le source cells output path).trans
          (ResourcePool.le_max_right _ _)
      · exact ResourcePool.le_max_left _ _

/-- The stored base and measured word enter the complete real native order-recovery program. -/
theorem recovered_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered source parameter phase cells output).Path) :
    (recovered source parameter phase cells output).resourcePool path ≤
      recoveredEnvelope kind N := by
  change ResourcePool.ofList ([(packBaseOp parameter cells).event] ++
    ((OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order).eventTrace path.2.1 ++
      ([(unpackOrderOp cells).event] ++
        (dispatch source parameter cells output).eventTrace path.2.2.2))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl
    (add_le_add (OrderRecovery.Native.nativeRecovery_into_pool_le
      (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1)
      (add_le_add le_rfl (dispatch_pool_le source parameter cells output path.2.2.2)))

/-- The known even exception counts actual flag writes, the literal load and the option pack. -/
theorem evenModulus_pool_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus cells output).Path) :
    (evenModulus cells output).resourcePool path ≤ evenEnvelope kind N := by
  change ResourcePool.ofList ([(clearActiveOp cells).event] ++
    ([(setActiveOp cells).event] ++
      ((ConstantWord.circuit cells.halfPower 2).eventTrace path.2.2.1 ++
        [(packOutputOp cells output).event]))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (ConstantWord.constantWord_pool_le cells.halfPower 2 path.2.2.1) le_rfl))

/-- Every complete actual factor-tail path fits the independently selected native event budget. -/
theorem code_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase cells output).Path) :
    (code source parameter phase cells output).resourcePool path ≤ eventEnvelope kind N := by
  have allPaths : ∀ selected : (code source parameter phase cells output).Path,
      (code source parameter phase cells output).resourcePool selected ≤ eventEnvelope kind N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code source parameter phase cells output = evenModulus cells output :=
        if_pos exceptional
      rw [same]
      simpa only [eventEnvelope, if_pos exceptional] using evenModulus_pool_le cells output
    · have same : code source parameter phase cells output =
          recovered source parameter phase cells output := if_neg exceptional
      rw [same]
      simpa only [eventEnvelope, if_neg exceptional] using
        recovered_pool_le source parameter phase cells output
  exact allPaths path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
