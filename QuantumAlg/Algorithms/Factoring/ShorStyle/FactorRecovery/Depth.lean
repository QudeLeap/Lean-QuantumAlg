/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Depth

/-!
# Complete serial native depth of stored-sample factor recovery

The real selected branch carries its own execution depth. Every runtime guard,
nominal conversion, literal initialization and result pack is included around
the full order, power and GCD routines. Bounds retain the original known-modulus
exception without adding any input-value or mathematical-success assumption.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual modular half-power precedes the complete scoped GCD-selection dependency chain. -/
theorem reduce_unitDepth_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce source cells output).Path) :
    (reduce source cells output).depth (fun _ => 1) path ≤ reduceDepth N := by
  exact Nat.add_le_add
    (NativeHalfPower.code_unitDepth_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1)
    (NativeHalfFactorScope.code_unitDepth_le (halfRead cells) output path.2)

/-- All five actual runtime predicates contribute one real serial native operation each. -/
theorem guardOrder_unitDepth (cells : Cells ctx N) (path : (guardOrder cells).Path) :
    (guardOrder cells).depth (fun _ => 1) path = 5 := rfl

private theorem checkedBranch_unitDepth_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).depth (fun _ => 1) path ≤
      max 1 (reduceDepth N) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.le_max_left _ _
      · exact (reduce_unitDepth_le source cells output path).trans (Nat.le_max_right _ _)

/-- The real guard precedes either actual reduction or actual none packaging. -/
theorem checkedOrder_unitDepth_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder source cells output).Path) :
    (checkedOrder source cells output).depth (fun _ => 1) path ≤ 5 + max 1 (reduceDepth N) :=
  Nat.add_le_add (guardOrder_unitDepth cells path.1).le
    (checkedBranch_unitDepth_le source cells output path.2)

/-- Stored early-factor priority uses the maximum of the two genuine continuation depths. -/
theorem dispatch_unitDepth_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch source parameter cells output).Path) :
    (dispatch source parameter cells output).depth (fun _ => 1) path ≤ dispatchDepth N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (checkedOrder_unitDepth_le source cells output path).trans (Nat.le_max_right _ _)
      · exact Nat.le_max_left _ _

/-- The complete real recovery includes both nominal conversions and all serial native work. -/
theorem recovered_unitDepth_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered source parameter phase cells output).Path) :
    (recovered source parameter phase cells output).depth (fun _ => 1) path ≤
      recoveredDepth N := by
  exact Nat.add_le_add_left
    (Nat.add_le_add (OrderRecovery.Native.nativeRecovery_into_unitDepth_le
      (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1)
      (Nat.add_le_add_left (dispatch_unitDepth_le source parameter cells output path.2.2.2) 1)) 1

/-- The original even-modulus exception still executes the full literal factor-two load. -/
theorem evenModulus_unitDepth_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus cells output).Path) :
    (evenModulus cells output).depth (fun _ => 1) path ≤ evenDepth N := by
  have loaded := ConstantWord.constantWord_depth_le cells.halfPower 2
    (fun _ => 1) path.2.2.1
  change (ConstantWord.circuit cells.halfPower 2).depth (fun _ => 1) path.2.2.1 ≤
    modulusBits N * (1 + 1) at loaded
  change 1 + (1 + ((ConstantWord.circuit cells.halfPower 2).depth
    (fun _ => 1) path.2.2.1 + 1)) ≤ _
  unfold evenDepth
  omega

/-- Every actual complete tail path fits the independently specified native unit-depth bound. -/
theorem code_unitDepth_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase cells output).Path) :
    (code source parameter phase cells output).depth (fun _ => 1) path ≤ depthBound N := by
  have allPaths : ∀ selected : (code source parameter phase cells output).Path,
      (code source parameter phase cells output).depth (fun _ => 1) selected ≤ depthBound N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code source parameter phase cells output = evenModulus cells output :=
        if_pos exceptional
      rw [same]
      simpa only [depthBound, if_pos exceptional] using evenModulus_unitDepth_le cells output
    · have same : code source parameter phase cells output =
          recovered source parameter phase cells output := if_neg exceptional
      rw [same]
      simpa only [depthBound, if_neg exceptional] using
        recovered_unitDepth_le source parameter phase cells output
  exact allPaths path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
