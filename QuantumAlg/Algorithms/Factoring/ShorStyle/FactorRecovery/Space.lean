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

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private lemma guardOrder_visited (cells : Cells ctx N) (path : (guardOrder (model := model)
    cells).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (guardOrder (model := model)
        cells).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx, ctx, ctx, ctx, ctx] at present
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

private lemma guardOrder_resident_le (cells : Cells ctx N) (path : (guardOrder (model := model)
    cells).Path) :
    (guardOrder (model := model) cells).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (guardOrder_visited cells path visited present) ▸ le_rfl

/-- Sequential power and GCD work fit the same complete resident scratch allowance. -/
lemma reduce_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce (model := model) source cells output).Path) :
    (reduce (model := model) source cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  refine (Circuit.peakResidentSpace_seq
    (NativeHalfPower.code (model := model) source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code (model := model) (halfRead cells) output) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeHalfPower.code_resident_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1).trans
        (fun axis => Nat.add_le_add_left (halfPower_space_le model.kind N axis) _)
  · exact (NativeHalfFactorScope.code_resident_le (halfRead cells) output path.2).trans
      (fun axis => Nat.add_le_add_left (halfFactor_space_le model.kind N axis) _)

private lemma checkedBranch_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells
            output))).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution :=
          model) (packOutputOp cells output)) path).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact reduce_resident_le source cells output path

/-- The real guard and selected reduction share the existing resident context. -/
lemma checkedOrder_resident_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder (model := model) source cells output).Path) :
    (checkedOrder (model := model) source cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  refine (Circuit.peakResidentSpace_seq (guardOrder (model := model) cells)
    (.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))) path).le.trans
            ?_
  apply SpacePool.max_le
  · exact (guardOrder_resident_le cells path.1).trans (fun _ => Nat.le_add_right _ _)
  · exact checkedBranch_resident_le source cells output path.2

/-- Both real stored early-factor branches preserve the same resident capacity bound. -/
lemma dispatch_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch (model := model) source parameter cells output).Path) :
    (dispatch (model := model) source parameter cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact checkedOrder_resident_le source cells output path
      · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution :=
          model) (packEarlyOp parameter output)) path).le.trans
          (fun _ => Nat.le_add_right _ _)

/-- Every actual order-recovery cell remains included in the full resident peak. -/
lemma recovered_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered (model := model) source parameter phase cells output).Path) :
    (recovered (model := model) source parameter phase cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (packBaseOp
      parameter cells))
    (.seq (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
        cells.base.toCStorageRef)
      phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells)) (dispatch (model :=
          model) source parameter cells output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution := model)
      (packBaseOp parameter cells)) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakResidentSpace_seq
      (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
          cells.base.toCStorageRef)
        phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells)) (dispatch (model :=
          model) source parameter cells output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact OrderRecovery.Native.nativeRecovery_into_resident_le
        (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1
    · refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model)
        (unpackOrderOp cells))
        (dispatch (model := model) source parameter cells output) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution :=
          model) (unpackOrderOp cells)) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact dispatch_resident_le source parameter cells output path.2.2.2

/-- The even exception writes its literal factor entirely within the existing resident space. -/
lemma evenModulus_resident_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus (model := model) cells output).Path) :
    (evenModulus (model := model) cells output).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (clearActiveOp
      cells))
    (.seq (BitWord.instruction (execution := model) (setActiveOp cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2) (BitWord.instruction
          (execution := model) (packOutputOp cells output))))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution := model)
      (clearActiveOp cells)) path.1).le
  · refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (setActiveOp
      cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2) (BitWord.instruction
          (execution := model) (packOutputOp cells output)))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution := model)
        (setActiveOp cells)) path.2.1).le
    · refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit (model := model) cells.halfPower
        2)
        (BitWord.instruction (execution := model) (packOutputOp cells output)) path.2.2).le.trans ?_
      exact SpacePool.max_le
        (ConstantWord.constantWord_resident_le cells.halfPower 2 path.2.2.1)
        (Circuit.peakResidentSpace_classical (BitWord.selectedApplication (execution := model)
            (packOutputOp cells output)) path.2.2.2).le

/-- Every actual complete tail path satisfies its independently specified resident space bound. -/
lemma code_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source parameter phase cells output).Path) :
    (code (model := model) source parameter phase cells output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  have allPaths : ∀ selected : (code (model := model) source parameter phase cells output).Path,
      (code (model := model) source parameter phase cells output).peakResidentSpace selected ≤
        ctx.residentSpace + spaceBound model.kind N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code (model := model) source parameter phase cells output = evenModulus (model
        := model) cells output :=
        if_pos exceptional
      rw [same]
      intro selected
      exact (evenModulus_resident_le cells output selected).trans (fun _ => Nat.le_add_right _ _)
    · have same : code (model := model) source parameter phase cells output =
          recovered (model := model) source parameter phase cells output := if_neg exceptional
      rw [same]
      exact recovered_resident_le source parameter phase cells output
  exact allPaths path

private lemma guardOrder_auxiliary_le (cells : Cells ctx N) (path : (guardOrder (model := model)
    cells).Path) :
    (guardOrder (model := model) cells).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (guardOrder_visited cells path visited present) ▸ le_rfl

/-- Sequential power and GCD work fit the same complete auxiliary scratch allowance. -/
lemma reduce_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (reduce (model := model) source cells output).Path) :
    (reduce (model := model) source cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (NativeHalfPower.code (model := model) source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code (model := model) (halfRead cells) output) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeHalfPower.code_auxiliary_le source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower path.1).trans
        (fun axis => Nat.add_le_add_left (halfPower_space_le model.kind N axis) _)
  · exact (NativeHalfFactorScope.code_auxiliary_le (halfRead cells) output path.2).trans
      (fun axis => Nat.add_le_add_left (halfFactor_space_le model.kind N axis) _)

private lemma checkedBranch_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))).Path) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells
            output))).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution :=
          model) (packOutputOp cells output)) path).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact reduce_auxiliary_le source cells output path

/-- The real guard and selected reduction share the existing auxiliary context. -/
lemma checkedOrder_auxiliary_le (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (checkedOrder (model := model) source cells output).Path) :
    (checkedOrder (model := model) source cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (guardOrder (model := model) cells)
    (.branch (activeRead cells)
      (fun value => if value.toBool then reduce (model := model) source cells output
        else BitWord.instruction (execution := model) (packOutputOp cells output))) path).le.trans
            ?_
  apply SpacePool.max_le
  · exact (guardOrder_auxiliary_le cells path.1).trans (fun _ => Nat.le_add_right _ _)
  · exact checkedBranch_auxiliary_le source cells output path.2

/-- Both real stored early-factor branches preserve the same auxiliary capacity bound. -/
lemma dispatch_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (dispatch (model := model) source parameter cells output).Path) :
    (dispatch (model := model) source parameter cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact checkedOrder_auxiliary_le source cells output path
      · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution :=
          model) (packEarlyOp parameter output)) path).le.trans
          (fun _ => Nat.le_add_right _ _)

/-- Every actual order-recovery cell remains included in the full auxiliary peak. -/
lemma recovered_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (recovered (model := model) source parameter phase cells output).Path) :
    (recovered (model := model) source parameter phase cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model) (packBaseOp
      parameter cells))
    (.seq (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
        cells.base.toCStorageRef)
      phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells)) (dispatch (model :=
          model) source parameter cells output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution := model)
      (packBaseOp parameter cells)) path.1).le.trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakAuxiliarySpace_seq
      (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
          cells.base.toCStorageRef)
        phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells)) (dispatch (model :=
          model) source parameter cells output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact OrderRecovery.Native.nativeRecovery_into_auxiliary_le
        (recoverySpec source) (.storage cells.base.toCStorageRef) phase cells.order path.2.1
    · refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model)
        (unpackOrderOp cells))
        (dispatch (model := model) source parameter cells output) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution :=
          model) (unpackOrderOp cells)) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact dispatch_auxiliary_le source parameter cells output path.2.2.2

/-- The even exception writes its literal factor entirely within the existing auxiliary space. -/
lemma evenModulus_auxiliary_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (evenModulus (model := model) cells output).Path) :
    (evenModulus (model := model) cells output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model) (clearActiveOp
      cells))
    (.seq (BitWord.instruction (execution := model) (setActiveOp cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2) (BitWord.instruction
          (execution := model) (packOutputOp cells output))))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution := model)
      (clearActiveOp cells)) path.1).le
  · refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model) (setActiveOp
      cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2) (BitWord.instruction
          (execution := model) (packOutputOp cells output)))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution :=
        model) (setActiveOp cells)) path.2.1).le
    · refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit (model := model)
        cells.halfPower 2)
        (BitWord.instruction (execution := model) (packOutputOp cells output)) path.2.2).le.trans ?_
      exact SpacePool.max_le
        (ConstantWord.constantWord_auxiliary_le cells.halfPower 2 path.2.2.1)
        (Circuit.peakAuxiliarySpace_classical (BitWord.selectedApplication (execution := model)
            (packOutputOp cells output)) path.2.2.2).le

/-- Every actual complete tail path satisfies the independent auxiliary space bound. -/
lemma code_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source parameter phase cells output).Path) :
    (code (model := model) source parameter phase cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  have allPaths : ∀ selected : (code (model := model) source parameter phase cells output).Path,
      (code (model := model) source parameter phase cells output).peakAuxiliarySpace selected ≤
        ctx.auxiliarySpace + spaceBound model.kind N := by
    by_cases exceptional : 2 < N ∧ Even N
    · have same : code (model := model) source parameter phase cells output = evenModulus (model
        := model) cells output :=
        if_pos exceptional
      rw [same]
      intro selected
      exact (evenModulus_auxiliary_le cells output selected).trans (fun _ => Nat.le_add_right _ _)
    · have same : code (model := model) source parameter phase cells output =
          recovered (model := model) source parameter phase cells output := if_neg exceptional
      rw [same]
      exact recovered_auxiliary_le source parameter phase cells output
  exact allPaths path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
