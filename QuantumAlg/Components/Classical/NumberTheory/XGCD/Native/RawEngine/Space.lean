/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Resources

/-!
# Complete live storage of the actual raw extended-Euclidean engine

The original zero word and seven state cells remain live through the guarded
loop. Each active slot allocates four scratch cells, reusing its product and
updated-coefficient words. The bound counts every original context entry and
all simultaneously live classical shapes, including at operand width zero.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent original zero, state, and shared active scratch storage. -/
def rawScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord width) +
    (((stateShapes width).map SpacePool.ofShape).sum +
      ((activeScratchShapes width).map SpacePool.ofShape).sum)

private theorem loop_visited (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat)
    (path : (Circuit.iterate count (guardedActive cells zero)).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈
      (Circuit.iterate count (guardedActive cells zero)).visitedContexts path) :
    visited = ctx ∨ ∃ index : Fin count,
      visited ∈ (guardedActive cells zero).visitedContexts (path index) := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin count =>
    (guardedActive cells zero).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with same | inner
  · exact Or.inl same
  · rcases List.mem_flatten.mp inner with ⟨contexts, listed, member⟩
    rcases List.mem_ofFn.mp listed with ⟨index, rfl⟩
    exact Or.inr ⟨index, member⟩

private theorem guarded_resident (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (path : (guardedActive cells zero).Path) :
    (guardedActive cells zero).peakResidentSpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_of_nonneg_left zero_le
      · exact xgcdNativeScopedActive_resident cells zero path

private theorem loop_resident (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat)
    (path : (Circuit.iterate count (guardedActive cells zero)).Path) :
    (Circuit.iterate count (guardedActive cells zero)).peakResidentSpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases loop_visited cells zero count path visited present with same | ⟨index, member⟩
  · subst visited
    exact le_add_of_nonneg_left zero_le
  · exact ((guardedActive cells zero).residentSpace_le_peak_of_visited
      (path index) visited member).trans (guarded_resident cells zero (path index))

private theorem initialization_resident (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).peakResidentSpace path = ctx.residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    have same : visited = ctx := by
      change visited ∈ [ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))) at present
      simpa only [List.mem_append, List.mem_singleton, or_self] using present
    rw [same]
  · exact (initializationBody cells input zero).input_residentSpace_le_peak path

private theorem outputs_resident (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (path : (copyRawOutputs cells outputs).Path) :
    (copyRawOutputs cells outputs).peakResidentSpace path = ctx.residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    have same : visited = ctx := by
      change visited ∈ [ctx] ++ ([ctx] ++ [ctx]) at present
      simpa only [List.mem_append, List.mem_singleton, or_self] using present
    rw [same]
  · exact (copyRawOutputs cells outputs).input_residentSpace_le_peak path

/-- Every actual scheduled resident peak includes all live scratch and caller entries. -/
theorem xgcdNativeScheduledRaw_resident_le (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (scheduledRawBody cells input zero outputs).Path) :
    (scheduledRawBody cells input zero outputs).peakResidentSpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (initializationBody cells input zero)
    (.seq (.iterate (Euclid.gcdFuel width) (guardedActive cells zero))
      (copyRawOutputs cells outputs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (initialization_resident cells input zero path.1).le.trans
      (le_add_of_nonneg_left zero_le)
  · refine (Circuit.peakResidentSpace_seq
      (.iterate (Euclid.gcdFuel width) (guardedActive cells zero))
      (copyRawOutputs cells outputs) path.2).le.trans ?_
    exact SpacePool.max_le (loop_resident cells zero (Euclid.gcdFuel width) path.2.1)
      ((outputs_resident cells outputs path.2.2).le.trans (le_add_of_nonneg_left zero_le))

/-- The seven real state cells stay live beside the maximum active resident scratch. -/
theorem xgcdNativeWithRawState_resident_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (withRawState input zero outputs).Path) :
    (withRawState input zero outputs).peakResidentSpace path ≤
      ((stateShapes width).map SpacePool.ofShape).sum +
        ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells (transport.liftInput input)
      (transport.liftInput zero) (outputs.transport transport))
    (((activeScratchShapes width).map SpacePool.ofShape).sum)
    (fun cells _ transport _ selected =>
      xgcdNativeScheduledRaw_resident_le cells _ _ _ selected) path

private theorem lexical_resident_le {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (additional : SpacePool kind)
    (bound : ∀ selected, body.peakResidentSpace selected ≤
      additional + (inner.addWorkspace key shape fresh).residentSpace)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).peakResidentSpace path ≤
      SpacePool.ofShape shape + additional + inner.residentSpace := by
  rw [Circuit.peakResidentSpace_workspace]
  apply SpacePool.max_le
  · exact le_add_of_nonneg_left zero_le
  · simpa only [RuntimeCtx.residentSpace_addWorkspace, add_assoc, add_comm, add_left_comm]
      using bound path

/-- The whole raw engine charges its actual zero word and every live resident allocation. -/
theorem xgcdNativeRawEngine_resident_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (path : (rawEngine input outputs).Path) :
    (rawEngine input outputs).peakResidentSpace path ≤
      rawScratchSpace kind width + ctx.residentSpace := by
  exact lexical_resident_le ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
    (withRawState
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)
    (((stateShapes width).map SpacePool.ofShape).sum +
      ((activeScratchShapes width).map SpacePool.ofShape).sum)
    (xgcdNativeWithRawState_resident_le
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero) path

private theorem guarded_auxiliary (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (path : (guardedActive cells zero).Path) :
    (guardedActive cells zero).peakAuxiliarySpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_of_nonneg_left zero_le
      · exact xgcdNativeScopedActive_auxiliary cells zero path

private theorem loop_auxiliary (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat)
    (path : (Circuit.iterate count (guardedActive cells zero)).Path) :
    (Circuit.iterate count (guardedActive cells zero)).peakAuxiliarySpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases loop_visited cells zero count path visited present with same | ⟨index, member⟩
  · subst visited
    exact le_add_of_nonneg_left zero_le
  · exact ((guardedActive cells zero).auxiliarySpace_le_peak_of_visited
      (path index) visited member).trans (guarded_auxiliary cells zero (path index))

private theorem initialization_auxiliary (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    have same : visited = ctx := by
      change visited ∈ [ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])))) at present
      simpa only [List.mem_append, List.mem_singleton, or_self] using present
    rw [same]
  · exact (initializationBody cells input zero).input_auxiliarySpace_le_peak path

private theorem outputs_auxiliary (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (path : (copyRawOutputs cells outputs).Path) :
    (copyRawOutputs cells outputs).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    have same : visited = ctx := by
      change visited ∈ [ctx] ++ ([ctx] ++ [ctx]) at present
      simpa only [List.mem_append, List.mem_singleton, or_self] using present
    rw [same]
  · exact (copyRawOutputs cells outputs).input_auxiliarySpace_le_peak path

/-- Every actual scheduled auxiliary peak includes all live scratch and caller entries. -/
theorem xgcdNativeScheduledRaw_auxiliary_le (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (scheduledRawBody cells input zero outputs).Path) :
    (scheduledRawBody cells input zero outputs).peakAuxiliarySpace path ≤
      ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (initializationBody cells input zero)
    (.seq (.iterate (Euclid.gcdFuel width) (guardedActive cells zero))
      (copyRawOutputs cells outputs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (initialization_auxiliary cells input zero path.1).le.trans
      (le_add_of_nonneg_left zero_le)
  · refine (Circuit.peakAuxiliarySpace_seq
      (.iterate (Euclid.gcdFuel width) (guardedActive cells zero))
      (copyRawOutputs cells outputs) path.2).le.trans ?_
    exact SpacePool.max_le (loop_auxiliary cells zero (Euclid.gcdFuel width) path.2.1)
      ((outputs_auxiliary cells outputs path.2.2).le.trans (le_add_of_nonneg_left zero_le))

/-- The seven real state cells stay live beside the maximum active auxiliary scratch. -/
theorem xgcdNativeWithRawState_auxiliary_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (withRawState input zero outputs).Path) :
    (withRawState input zero outputs).peakAuxiliarySpace path ≤
      ((stateShapes width).map SpacePool.ofShape).sum +
        ((activeScratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells (transport.liftInput input)
      (transport.liftInput zero) (outputs.transport transport))
    (((activeScratchShapes width).map SpacePool.ofShape).sum)
    (fun cells _ transport _ selected =>
      xgcdNativeScheduledRaw_auxiliary_le cells _ _ _ selected) path

private theorem lexical_auxiliary_le {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (additional : SpacePool kind)
    (bound : ∀ selected, body.peakAuxiliarySpace selected ≤
      additional + (inner.addWorkspace key shape fresh).auxiliarySpace)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).peakAuxiliarySpace path ≤
      SpacePool.ofShape shape + additional + inner.auxiliarySpace := by
  rw [Circuit.peakAuxiliarySpace_workspace]
  apply SpacePool.max_le
  · exact le_add_of_nonneg_left zero_le
  · simpa only [RuntimeCtx.auxiliarySpace_addWorkspace, add_assoc, add_comm, add_left_comm]
      using bound path

/-- The whole raw engine charges its actual zero word and every live auxiliary allocation. -/
theorem xgcdNativeRawEngine_auxiliary_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (path : (rawEngine input outputs).Path) :
    (rawEngine input outputs).peakAuxiliarySpace path ≤
      rawScratchSpace kind width + ctx.auxiliarySpace := by
  exact lexical_auxiliary_le ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
    (withRawState
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)
    (((stateShapes width).map SpacePool.ofShape).sum +
      ((activeScratchShapes width).map SpacePool.ofShape).sum)
    (xgcdNativeWithRawState_auxiliary_le
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero) path

/-- The original full scratch formula counts the reused coefficient cells only once. -/
theorem xgcdNativeRawScratch_classicalBits (kind : ProblemKind) (width : Nat) :
    rawScratchSpace kind width .classicalBits =
      5 * width + 7 * PureXGCD.executionCoefficientWidth width + 1 := by
  simp [rawScratchSpace, stateShapes, activeScratchShapes, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
