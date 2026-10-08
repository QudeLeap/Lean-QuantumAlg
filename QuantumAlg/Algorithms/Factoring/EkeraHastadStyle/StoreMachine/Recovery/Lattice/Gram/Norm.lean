/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh

/-!
# Actual lattice squared-norm refresh

Squared-norm refresh is the self-dot specialization of the shared five-instruction
refresh. Its value, complete execution, caller frame and borrowed restoration
are derived from that same circuit, with arbitrary initial scratch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNormRefresh

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Caller-owned accumulator and product word for one norm refresh. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the norm value. -/
  norm : CWriteRef ctx (.unsignedWord width)
  normRole : norm.toCStorageRef.role = .workspace
  /-- Writable cell for the product value. -/
  product : CWriteRef ctx (.unsignedWord width)
  productRole : product.toCStorageRef.role = .workspace

/-- Separation for overwriting and then accumulating one point squared norm. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (point : LatticeState.PointRefs ctx width) (refs : Refs ctx width) : Prop where
  dot : LatticeDot.PointDotSeparation point point refs.norm refs.product

/-- View the caller's norm cells as the shared dot-refresh outputs. -/
def dotRefs (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.norm
  dotRole := refs.normRole
  product := refs.product
  productRole := refs.productRole

/-- The actual norm circuit applies the shared five-instruction refresh to the same point twice. -/
def refreshInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  LatticeDotRefresh.refreshInto (model := model) point point (dotRefs refs)

/-- Actual chronological stores of the shared self-dot refresh. -/
def refreshStore (point : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  LatticeDotRefresh.refreshStore point point (dotRefs refs) store

/-- The complete actual refresh execution preserves history and quantum-reference blocks. -/
theorem refreshInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) point refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := LatticeDotRefresh.refreshStep (model := model)
          point point (dotRefs refs) entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact LatticeDotRefresh.refreshInto_execute point point (dotRefs refs) Reference state

/-- Only the caller's norm and product cells are changed by the actual refresh. -/
theorem refreshInto_callerFrame (point : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoidsNorm : refs.norm.key ∉ other.storageKeys)
    (avoidsProduct : refs.product.key ∉ other.storageKeys) :
    (refreshStore point refs store).read other = store.read other := by
  exact LatticeDotRefresh.refreshInto_callerFrame point point (dotRefs refs)
    store other avoidsNorm avoidsProduct

/-- The actual output represents the squared norm and preserves the original point. -/
theorem refreshInto_correct (point : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (separation : Separation point refs) (store : Store ctx)
    (pointValue : NumberTheory.IntegerPoint3)
    (pointRep : LatticeArithmetic.PointRawRepresents store point pointValue) :
    RawSignedRepresents ((refreshStore point refs store).read (writeInput refs.norm))
        (NumberTheory.integerPointSquaredNorm pointValue : Int) ∧
      LatticeArithmetic.PointRawRepresents (refreshStore point refs store) point pointValue := by
  have dot := LatticeDotRefresh.refreshInto_correct point point (dotRefs refs) ⟨separation.dot⟩
    store pointValue pointValue pointRep pointRep
  rw [NumberTheory.integerPointDot_self] at dot
  exact ⟨dot.1, dot.2.1⟩

/-- The actual norm refresh restores all borrowed correlations without a state-output premise. -/
theorem refreshInto_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) point refs).BorrowedRestored Reference state
      ((refreshInto (model := model) point refs).execute Reference state) := by
  exact LatticeDotRefresh.refreshInto_borrowedRestored point point (dotRefs refs) Reference state

/-- Five actual native instructions overwrite and accumulate the squared norm. -/
theorem refreshInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) point refs).Path) :
    (refreshInto (model := model) point refs).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width))] :=
  LatticeDotRefresh.refreshInto_events point point (dotRefs refs) path

/-- All five native operations remain sequentially dependent. -/
theorem refreshInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) point refs).Path) :
    (refreshInto (model := model) point refs).depth (fun _ => 1) path = 5 :=
  LatticeDotRefresh.refreshInto_depth point point (dotRefs refs) path

/-- The refresh visits only the complete original live context. -/
theorem refreshInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) point refs).Path) :
    (refreshInto (model := model) point refs).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx] :=
  LatticeDotRefresh.refreshInto_visited point point (dotRefs refs) path

/-- Resident space includes all original quantum systems and the two existing cells. -/
theorem refreshInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) point refs).Path) :
    (refreshInto (model := model) point refs).peakResidentSpace path ≤ ctx.residentSpace := by
  exact LatticeDotRefresh.refreshInto_resident_le point point (dotRefs refs) path

/-- Auxiliary accounting uses the same supplied roles, with no temporary allocation. -/
theorem refreshInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (point : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) point refs).Path) :
    (refreshInto (model := model) point refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  exact LatticeDotRefresh.refreshInto_auxiliary_le point point (dotRefs refs) path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNormRefresh
