/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# All live scratch of the actual stored-sample factor tail

Complete order recovery, modular half-power and scoped GCD selection run
sequentially and release their own scratch. The independent order-recovery
capacity dominates their individual live peaks. All surrounding runtime
checks, nominal conversions and packaging use existing cells. The seven
outer tail cells remain in the actual input context and are counted by the
scope owner when this tail is placed under those real allocations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem guardOrder_visited (cells : Cells ctx N) (path : (guardOrder cells).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (guardOrder cells).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx, ctx, ctx, ctx, ctx] at present
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

private theorem guardOrder_resident_le (cells : Cells ctx N) (path : (guardOrder cells).Path) :
    (guardOrder cells).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (guardOrder_visited cells path visited present) ▸ le_rfl

/-- Sequential power and GCD work fit the same complete resident scratch allowance. -/
theorem reduce_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce source cells output).Path) :
    (reduce source cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq
    (NativeHalfPower.code source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code (halfRead cells) output) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeHalfPower.code_resident_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1).trans
        (fun axis => Nat.add_le_add_left (halfPower_space_le kind N axis) _)
  · exact (NativeHalfFactorScope.code_resident_le (halfRead cells) output path.2).trans
      (fun axis => Nat.add_le_add_left (halfFactor_space_le kind N axis) _)

private theorem checkedBranch_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.peakResidentSpace_classical (packOutputOp cells output) path).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact reduce_resident_le source cells output path

/-- The real guard and selected reduction share the existing resident context. -/
theorem checkedOrder_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder source cells output).Path) :
    (checkedOrder source cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq (guardOrder cells)
    (.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (guardOrder_resident_le cells path.1).trans (fun _ => Nat.le_add_right _ _)
  · exact checkedBranch_resident_le source cells output path.2

/-- Both real stored early-factor branches preserve the same resident capacity bound. -/
theorem dispatch_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch source parameter cells output).Path) :
    (dispatch source parameter cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact checkedOrder_resident_le source cells output path
      · exact (Circuit.peakResidentSpace_classical (packEarlyOp parameter output) path).le.trans
          (fun _ => Nat.le_add_right _ _)

/-- Every actual order-recovery cell remains included in the full resident peak. -/
theorem recovered_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered source parameter phase cells output).Path) :
    (recovered source parameter phase cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq (.classical (packBaseOp parameter cells))
    (.seq (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakResidentSpace_classical (packBaseOp parameter cells) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakResidentSpace_seq
      (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
        phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact OrderRecovery.Native.nativeRecovery_into_resident_le
        (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1
    · refine (Circuit.peakResidentSpace_seq (.classical (unpackOrderOp cells))
        (dispatch source parameter cells output) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakResidentSpace_classical (unpackOrderOp cells) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact dispatch_resident_le source parameter cells output path.2.2.2

/-- The even exception writes its literal factor entirely within the existing resident space. -/
theorem evenModulus_resident_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus cells output).Path) :
    (evenModulus cells output).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (.classical (clearActiveOp cells))
    (.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output))))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakResidentSpace_classical (clearActiveOp cells) path.1).le
  · refine (Circuit.peakResidentSpace_seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output)))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (Circuit.peakResidentSpace_classical (setActiveOp cells) path.2.1).le
    · refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit cells.halfPower 2)
        (.classical (packOutputOp cells output)) path.2.2).le.trans ?_
      exact SpacePool.max_le
        (ConstantWord.constantWord_resident_le cells.halfPower 2 path.2.2.1)
        (Circuit.peakResidentSpace_classical (packOutputOp cells output) path.2.2.2).le

/-- Every actual complete tail path satisfies its independently specified resident space bound. -/
theorem code_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase cells output).Path) :
    (code source parameter phase cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  have allPaths : ∀ selected : (code source parameter phase cells output).Path,
      (code source parameter phase cells output).peakResidentSpace selected ≤
        ctx.residentSpace + spaceBound kind N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code source parameter phase cells output = evenModulus cells output :=
        if_pos exceptional
      rw [same]
      intro selected
      exact (evenModulus_resident_le cells output selected).trans (fun _ => Nat.le_add_right _ _)
    · have same : code source parameter phase cells output =
          recovered source parameter phase cells output := if_neg exceptional
      rw [same]
      exact recovered_resident_le source parameter phase cells output
  exact allPaths path

private theorem guardOrder_auxiliary_le (cells : Cells ctx N) (path : (guardOrder cells).Path) :
    (guardOrder cells).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (guardOrder_visited cells path visited present) ▸ le_rfl

/-- Sequential power and GCD work fit the same complete auxiliary scratch allowance. -/
theorem reduce_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce source cells output).Path) :
    (reduce source cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (NativeHalfPower.code source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code (halfRead cells) output) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeHalfPower.code_auxiliary_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1).trans
        (fun axis => Nat.add_le_add_left (halfPower_space_le kind N axis) _)
  · exact (NativeHalfFactorScope.code_auxiliary_le (halfRead cells) output path.2).trans
      (fun axis => Nat.add_le_add_left (halfFactor_space_le kind N axis) _)

private theorem checkedBranch_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.peakAuxiliarySpace_classical (packOutputOp cells output) path).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact reduce_auxiliary_le source cells output path

/-- The real guard and selected reduction share the existing auxiliary context. -/
theorem checkedOrder_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder source cells output).Path) :
    (checkedOrder source cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (guardOrder cells)
    (.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (guardOrder_auxiliary_le cells path.1).trans (fun _ => Nat.le_add_right _ _)
  · exact checkedBranch_auxiliary_le source cells output path.2

/-- Both real stored early-factor branches preserve the same auxiliary capacity bound. -/
theorem dispatch_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch source parameter cells output).Path) :
    (dispatch source parameter cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact checkedOrder_auxiliary_le source cells output path
      · exact (Circuit.peakAuxiliarySpace_classical (packEarlyOp parameter output) path).le.trans
          (fun _ => Nat.le_add_right _ _)

/-- Every actual order-recovery cell remains included in the full auxiliary peak. -/
theorem recovered_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered source parameter phase cells output).Path) :
    (recovered source parameter phase cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (.classical (packBaseOp parameter cells))
    (.seq (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakAuxiliarySpace_classical (packBaseOp parameter cells) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakAuxiliarySpace_seq
      (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
        phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact OrderRecovery.Native.nativeRecovery_into_auxiliary_le
        (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1
    · refine (Circuit.peakAuxiliarySpace_seq (.classical (unpackOrderOp cells))
        (dispatch source parameter cells output) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakAuxiliarySpace_classical (unpackOrderOp cells) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact dispatch_auxiliary_le source parameter cells output path.2.2.2

/-- The even exception writes its literal factor entirely within the existing auxiliary space. -/
theorem evenModulus_auxiliary_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus cells output).Path) :
    (evenModulus cells output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (.classical (clearActiveOp cells))
    (.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output))))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakAuxiliarySpace_classical (clearActiveOp cells) path.1).le
  · refine (Circuit.peakAuxiliarySpace_seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2) (.classical (packOutputOp cells output)))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (Circuit.peakAuxiliarySpace_classical (setActiveOp cells) path.2.1).le
    · refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit cells.halfPower 2)
        (.classical (packOutputOp cells output)) path.2.2).le.trans ?_
      exact SpacePool.max_le
        (ConstantWord.constantWord_auxiliary_le cells.halfPower 2 path.2.2.1)
        (Circuit.peakAuxiliarySpace_classical (packOutputOp cells output) path.2.2.2).le

/-- Every actual complete tail path satisfies the independent auxiliary space bound. -/
theorem code_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase cells output).Path) :
    (code source parameter phase cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  have allPaths : ∀ selected : (code source parameter phase cells output).Path,
      (code source parameter phase cells output).peakAuxiliarySpace selected ≤
        ctx.auxiliarySpace + spaceBound kind N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code source parameter phase cells output = evenModulus cells output :=
        if_pos exceptional
      rw [same]
      intro selected
      exact (evenModulus_auxiliary_le cells output selected).trans (fun _ => Nat.le_add_right _ _)
    · have same : code source parameter phase cells output =
          recovered source parameter phase cells output := if_neg exceptional
      rw [same]
      exact recovered_auxiliary_le source parameter phase cells output
  exact allPaths path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
